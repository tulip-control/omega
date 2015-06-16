"""Symbolic automaton.

Including bitblasting of first-order to bitvector logic,
and transformation to BDD nodes.
"""
import copy
from itertools import chain
import logging
import pprint
import dd.bdd
from omega.logic import syntax
import natsort
from openpromela import bdd as _bdd
from openpromela import bitvector


logger = logging.getLogger(__name__)


class Automaton(object):
    """Transition relation, initial condition, and hidden variables.

    The user defines the attributes:

      - vars: `dict` that maps each var to `dict` of attr
      - init: initial condition
      - action: transition relation
      - win: winning condition

    Call the method `build` to generate the below.


    User-defined attributes
    =======================

    The attributes `init`, `action`, `win` are
    lists of formulae as `str` or BDD nodes.

    The attribute `vars` is a `dict` that
    maps each integer variable name to a `dict` with keys:

      - `"type": "boolean" or "modwrap" or "saturating"`
      - `"dom": (min, max)`, range of integer
      - `"owner": "env" or "sys"`
      - `"init"`: has suitable `__str__` (and is optional)


    Auto-generated attributes
    =========================

    The method `build` adds the keys:

      - `"bitnames"`: `list`
      - `"signed"`: `True` if signed integer
      - `"width"`: `len(bitnames)`

    Each of the following is a `set` of BDD levels:

      - uvars
      - upvars
      - evars
      - epvars
      - prime_vars: `dict` that maps each unprimed to a primed var
      - unprime_vars: `dict` that maps eacn primed to an unprimed var

    Prefix meaning:

    u = universally quantified
    e = existentially quantified
    p = primed (absence means unprimed)


    Reference
    =========

    Schneider K.
        "Verification of reactive systems"
        Springer, 2004

    Lamport L.
        "The temporal logic of actions"
        ACM Transactions on Programming
        Languages and Systems (TOPLAS),
        Vol.16, No.3, pp.872--923, 1994
    """

    def __init__(self):
        # vars
        self.vars = dict()
        # subsets of vars: auto-populated
        self.uvars = set()  # unprimed env
        self.upvars = set()  # primed env
        self.evars = set()  # unprimed sys
        self.epvars = set()  # primed sys
        # future: hidden, node vars
        # map between primed and unprimed
        self.prime = dict()
        self.unprime = dict()
        # formulae
        self.init = dict(env=list(), sys=list())
        self.action = dict(env=list(), sys=list())
        self.win = dict(env=list(), sys=list())  # GF
        # aux
        self.bdd = dd.BDD()  # init only to help static analysis

    def __copy__(self):
        a = Automaton()
        a.vars = copy.deepcopy(self.vars)
        a.init = copy.deepcopy(self.init)
        a.action = copy.deepcopy(self.action)
        a.win = copy.deepcopy(self.win)
        return a

    def __str__(self):
        c = [
            'Symbolic automaton:',
            40 * '=',
            '',
            'variables:',
            '{dvars}',
            '']
        if self.init['env']:
            c.extend([
                'ENV INIT',
                '{env_init}',
                ''])
        if self.action['env']:
            c.extend([
                'ENV ACTION',
                '{env_action}',
                ''])
        if self.win['env']:
            c.extend([
                'ENV WIN',
                '{env_win}',
                ''])
        if self.init['sys']:
            c.extend([
                'SYS INIT',
                '{sys_init}',
                ''])
        if self.action['sys']:
            c.extend([
                'SYS ACTION',
                '{sys_action}',
                ''])
        if self.win['sys']:
            c.extend([
                'SYS WIN',
                '{sys_win}',
                ''])
        return '\n'.join(c).format(
                dvars=pprint.pformat(self.vars),
                env_init=_join(self.init['env']),
                env_action=_join(self.action['env']),
                env_win=_join(self.win['env']),
                sys_init=_join(self.init['sys']),
                sys_action=_join(self.action['sys']),
                sys_win=_join(self.win['sys']))

    def dumps(self):
        d = dict(vars=self.vars, init=self.init,
                 action=self.action, win=self.win)
        return repr(d)

    def build(self, bdd=None):
        """Return `Automaton` with formulae as BDD nodes.

        Bitblast variables, interleaved order,
        then prime them.

        @param bdd: use this `BDD`, instead of a fresh one
        @type bdd: `dd.bdd.BDD`
        """
        aut = _bitblast(self)
        aut = _bitvector_to_bdd(aut, bdd)
        return aut

    def assert_consistent(self):
        # is i/o partition ?
        assert not self.env_vars.intersection(self.sys_vars)
        assert set(self.vars) == self.sys_vars.union(self.env_vars)

    def update(self, attr, d):
        """Add formulae from `dict` `d`."""
        r = getattr(self, attr)
        r['env'].extend(d['env'])
        r['sys'].extend(d['sys'])

    def add_expr(self, e):
        """Add first-order formula."""
        # the bitblaster understands priming
        # the prefix parser treats primed bits as fresh
        # so suffice it for t to contain unprimed only
        t = self.vars
        s = bitvector.bitblast(e, t)
        u = _bdd.add_expr(s, self.bdd)
        return u


def _bitblast(aut):
    """Return `Automaton` with bitvector formulae.

    For each integer, the corresponding list of
    bitnames is added to the symbol table (attr `vars`).

    @type aut: `Automaton`
    """
    aut = copy.copy(aut)
    t, init, safety = bitvector.bitblast_table(aut.vars)
    aut.update('init', init)
    aut.update('action', safety)
    # conjoin to avoid it later over BDD nodes
    _conj_owner(aut, 'env')
    _conj_owner(aut, 'sys')
    a = Automaton()
    a.vars = t
    # TODO: replace GR(1) syntax check
    # spec.check_syntax()
    _bitblast_owner(aut, a, 'env', t)
    _bitblast_owner(aut, a, 'sys', t)
    return a


def _conj_owner(aut, owner):
    aut.init[owner] = [syntax.conj(aut.init[owner])]
    aut.action[owner] = [syntax.conj(aut.action[owner])]


def _bitblast_owner(aut, a, owner, t):
    """Bitblast init, action, win of `owner`."""
    def f(x):
        return bitvector.bitblast(x, t)
    a.init[owner] = map(f, aut.init[owner])
    a.action[owner] = map(f, aut.action[owner])
    a.win[owner] = map(f, aut.win[owner])


def _bitvector_to_bdd(aut, bdd=None):
    """Return `Automaton` with BDD formulae.

    @type aut: `Automaton`
    @type bdd: `dd.bdd.BDD`
    """
    dvars = aut.vars
    dbits = bitvector.list_bits(dvars)
    ubits = set(b for b, d in dbits.iteritems()
                if d['owner'] == 'env')
    # use fresh `BDD` ?
    if bdd is None:
        ordbits = _pick_var_order(dbits)
        order, prime, partition = _partition_vars(ordbits, ubits)
        bdd = dd.bdd.BDD(order)
    else:
        # check no missing vars,
        # including primed
        pbits, _, _ = _partition_vars(dbits, ubits)
        bdd_bits = bdd.ordering
        missing = set(pbits).difference(bdd_bits)
        assert not missing, (missing, pbits, bdd_bits)
        # extract order and partition
        prime, partition = _extract_partition(bdd.ordering, ubits)
    # bundle as:
    a = Automaton()
    a.bdd = bdd
    # vars
    a.vars = copy.deepcopy(dvars)
    a.uvars = partition['uvars']
    a.upvars = partition['upvars']
    a.evars = partition['evars']
    a.epvars = partition['epvars']
    # priming
    a.prime = prime
    a.unprime = {v: k for k, v in prime.iteritems()}
    # slugsin -> BDD
    for owner in ('env', 'sys'):
        _to_bdd(aut.init[owner], a.init[owner], bdd)
        _to_bdd(aut.action[owner], a.action[owner], bdd)
        _to_bdd(aut.win[owner], a.win[owner], bdd)
    # bdd.collect_garbage()
    return a


def _to_bdd(a, b, bdd):
    for s in a:
        u = _bdd.add_expr(s, bdd)
        # bdd.incref(u)
        b.append(u)


def _pick_var_order(dvars):
    """Order the variables in `dvars`."""
    # fix an order for unprimed vars or bits
    ordvars = natsort.natsorted(dvars)
    return ordvars


def _partition_vars(ordvars, uvars, suffix="'"):
    """Return primed and unprimed BDD levels.

    @param ordvars: `list` of variable names as `str`
    @param uv: universally quantified subset of `v`

    @return: (d, prime, uvars, upvars, evars, epvars)
      - d: `dict` that maps each var name to a level
      - prime: `dict` that maps unprimed to primed var levels
      - uvars/upvars (evars/epvars): `set` of
        universally (existentially) quantified
        un/primed variables as levels
    """
    d = dict()
    prime = dict()
    for i, var in enumerate(ordvars):
        j = 2 * i
        primed = var + suffix
        d[var] = j
        d[primed] = j + 1
        prime[j] = j + 1
    evars = {var for var in ordvars if var not in uvars}
    uj = map(d.get, uvars)
    ej = map(d.get, evars)
    upj = map(prime.get, uj)
    epj = map(prime.get, ej)
    # bundle
    c = [uj, upj, ej, epj]
    uj, upj, ej, epj = map(set, c)
    partition = dict(uvars=uj, upvars=upj,
                     evars=ej, epvars=epj)
    return d, prime, partition


def _prime_and_order_table(t, suffix="'"):
    """Return ordered table of primed and unprimed variables.

    The table maps each (integer or Boolean) variable to
    a `dict` of attributes (same as `t`).
    The attributes include `"bitnames"`.

    The following attributes are added:

      - level: index among ordered prime and unprimed integers
      - len: number of values the variable can take

    @param t: table of unprimed variables as `str`
    @type t: `dict`
    @param suffix: primed var = unprimed var + suffix
    @type suffix: `str`

    @rtype: `dict` from `str` to `dict`
    """
    ordvars = natsort.natsorted(t)
    dvars = dict()
    for i, var in enumerate(ordvars):
        d = t[var]
        j = 2 * i
        dtype = d['type']
        if dtype == 'int':
            bits = d['bitnames']
        elif dtype == 'bool':
            bits = [var]
        m = 2**len(bits)
        primed = var + suffix
        pbits = [bit + suffix for bit in bits]
        k = j + 1
        # copy attr
        dvars[var] = dict(d)
        dvars[primed] = dict(d)
        # update attr
        dvars[var].update(level=j, len=m, bitnames=bits)
        dvars[primed].update(level=k, len=m, bitnames=pbits)
    return dvars


def _extract_partition(dbits, ubits):
    """Return partition, given both primed and unprimed bits.

    @param all_bits: `BDD.ordering` that maps each bit to a level
    @type all_bits: `dict`
    @param ubits: universally quantified unprimed bits
    @type ubits: `set`

    @rtype: `dict`
    """
    suffix = "'"
    diff = set(ubits).difference(dbits)
    assert not diff, (diff, ubits, dbits)
    uvars = set()
    upvars = set()
    evars = set()
    epvars = set()
    for bit, i in dbits.iteritems():
        primed = bit.endswith(suffix)
        if primed:
            s = bit[:-1]
        else:
            s = bit
        universal = (s in ubits)
        if universal:
            if primed:
                upvars.add(bit)
            else:
                uvars.add(bit)
        else:
            if primed:
                epvars.add(bit)
            else:
                evars.add(bit)
    prime = dict()
    for bit in chain(uvars, evars):
        pbit = bit + suffix
        # not primed ?
        if pbit not in dbits:
            continue
        # primed bit
        uj = dbits[bit]
        pj = dbits[pbit]
        prime[uj] = pj
    uj = map(dbits.get, uvars)
    upj = map(dbits.get, upvars)
    ej = map(dbits.get, evars)
    epj = map(dbits.get, epvars)
    partition = dict(uvars=uj, upvars=upj,
                     evars=ej, epvars=epj)
    # check adjacency of unprimed-primed pairs
    for x, y in prime.iteritems():
        assert abs(x - y) == 1, (
            'The variables: {c} are not adjacent.\n'
            'Primed and unprimed vars must be adjacent in '
            'the given BDD.').format(c=(x, y))
    return prime, partition


def _join(c):
    """Return `str` with one element of `c` per line."""
    return '\n'.join(str(x) for x in c)
