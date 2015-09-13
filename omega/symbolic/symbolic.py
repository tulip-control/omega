"""Symbolic automaton.

Including bitblasting of first-order to bitvector logic,
and transformation to BDD nodes.
"""
import copy
from itertools import chain
import logging
import pprint
import dd.bdd
import natsort
from omega.logic import syntax
from omega.symbolic import bdd as _bdd
from omega.logic import bitvector as bv


logger = logging.getLogger(__name__)


class Automaton(object):
    """Transition relation, initial condition, and hidden variables.

    The user defines the attributes:

      - vars: `dict` that maps each var to `dict` of attr
      - init: initial condition
      - action: transition relation
      - win: winning condition
      - acceptance: `str` that describes `win`,
          for example `'Streett(1)'`

    Each of `init, action` is a `dict(env=list(), sys=list())`,
    and `win` is a `{'<>[]': list(), '[]<>': list()}`
    The lists contain formulae, as strings when populating the attributes.
    Call the method `build` to convert the formulae to BDD nodes,
    and generate the below.


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
      - ubvars
      - evars
      - epvars
      - ebvars
      - uevars
      - uepvars
      - prime: `dict` that maps each unprimed to a primed var
      - unprime: `dict` that maps eacn primed to an unprimed var

    Prefix meaning:

    u = universally quantified
    e = existentially quantified
    p = primed (absence means unprimed)
    b = both primed and unprimed


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
        self.ubvars = set()  # both primed and unprimed env
        self.evars = set()  # unprimed sys
        self.epvars = set()  # primed sys
        self.ebvars = set()  # both primed and unprimed env
        self.uevars = set()  # all unprimed vars
        self.uepvars = set()  # all primed vars
        # future: hidden, node vars
        # map between primed and unprimed
        self.prime = dict()
        self.unprime = dict()
        # formulae
        self.init = dict(env=list(), sys=list())
        self.action = dict(env=list(), sys=list())
        self.win = {'<>[]': list(), '[]<>': list()}
        self.acceptance = 'Streett(1)'
        # aux
        self.bdd = dd.bdd.BDD()  # init only to help static analysis

    def __copy__(self):
        a = Automaton()
        a.vars = copy.deepcopy(self.vars)
        a.init = copy.deepcopy(self.init)
        a.action = copy.deepcopy(self.action)
        a.win = copy.deepcopy(self.win)
        a.acceptance = self.acceptance
        return a

    def __del__(self):
        del self.init
        del self.action
        del self.win

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
                'ENV INIT:',
                '{env_init}',
                ''])
        if self.action['env']:
            c.extend([
                'ENV ACTION:',
                '{env_action}',
                ''])
        if self.init['sys']:
            c.extend([
                'SYS INIT:',
                '{sys_init}',
                ''])
        if self.action['sys']:
            c.extend([
                'SYS ACTION:',
                '{sys_action}',
                ''])
        if self.win['<>[]']:
            c.extend([
                '<>[] (persistence):',
                '{fg}',
                ''])
        if self.win['[]<>']:
            c.extend([
                '[]<> (recurrence):',
                '{gf}',
                ''])
        return '\n'.join(c).format(
                dvars=pprint.pformat(self.vars),
                env_init=_join(self.init['env']),
                env_action=_join(self.action['env']),
                fg=_join(self.win['<>[]']),
                sys_init=_join(self.init['sys']),
                sys_action=_join(self.action['sys']),
                gf=_join(self.win['[]<>']))

    def dumps(self):
        """Return `repr` of a `dict` with the attributes."""
        d = dict(vars=self.vars, init=self.init,
                 action=self.action, win=self.win)
        return repr(d)

    def build(self, bdd=None, add=True):
        """Return `Automaton` with formulae as BDD nodes.

        Bitblast variables, interleaved order,
        then prime them.

        @param bdd: use this `BDD`, instead of a fresh one
        @type bdd: `dd.bdd.BDD`
        @param add: insert any missing variables as new to `bdd`
        """
        aut = _bitblast(self)
        aut = _bitvector_to_bdd(aut, bdd, add)
        return aut

    def assert_consistent(self, built=False):
        """Raise `AssertionError` if not well-formed.

        @param built: if `True`, then assert `build` has been called.
        """
        # check attributes
        for d in (self.init, self.action, self.win):
            for k, v in d.iteritems():
                for u in v:
                    if built:
                        assert u in self.bdd, u
                    else:
                        assert isinstance(u, basestring)
        if not built:
            return
        # bdd initialized ?
        assert self.bdd.vars is not None
        if self.vars:
            assert self.uevars

    def update(self, attr, d):
        """Add formulae from `dict` `d`."""
        r = getattr(self, attr)
        if attr in ('init', 'action'):
            r['env'].extend(d['env'])
            r['sys'].extend(d['sys'])
        elif attr == 'win':
            r['<>[]'].extend(d['<>[]'])
            r['[]<>'].extend(d['[]<>'])
        else:
            raise Exception('unknown attr "{a}"'.format(a=attr))

    def conjoin(self, as_what):
        """Conjoin attributes.

        @param as_what: `'bdd' or 'prefix' or 'infix'`
        """
        _conj_owner(self, 'env', as_what)
        _conj_owner(self, 'sys', as_what)

    def add_expr(self, e):
        """Add first-order formula."""
        # the bitblaster understands priming
        # the prefix parser treats primed bits as fresh
        # so suffice it for t to contain unprimed only
        t = self.vars
        s = bv.bitblast(e, t)
        u = _bdd.add_expr(s, self.bdd)
        return u


def cofactor(f, var, value, bdd, table):
    """Cofactor integer variable."""
    assert var in table, var
    var_bits = bv.var_to_twos_complement(var, table)
    int_bits = bv.int_to_twos_complement(value)
    p, q = bv.equalize_width(var_bits, int_bits)
    values = dict()
    for u, v in zip(p, q):
        # primed ?
        if u.isdigit():
            assert u == v, (u, v)
        else:
            values[u] = bool(int(v))
    # take cofactor
    h = bdd.cofactor(f, values)
    return h


def fill_blanks(aut, as_bdd=False, rabin=False):
    """Add `"True"` to empty attributes `init`, `action`, `win`.

    @param as_bdd: if `True`, then represent `"True"` as `1`
    """
    if as_bdd:
        true = aut.bdd.True
        false = aut.bdd.False
    else:
        true = 'True'
        false = 'False'
    for d in (aut.init, aut.action):
        for k, v in d.iteritems():
            if not v:
                d[k] = [true]
    if not aut.win['<>[]']:
        if rabin:
            aut.win['<>[]'] = [true]
        else:
            aut.win['<>[]'] = [false]
    if not aut.win['[]<>']:
        aut.win['[]<>'] = [true]
    # post-condition
    for d in (aut.init, aut.action, aut.win):
        for k in d:
            assert len(d[k]) > 0


def _bitblast(aut):
    """Return `Automaton` with bitvector formulae.

    For each integer, the corresponding list of
    bitnames is added to the symbol table (attr `vars`).

    @type aut: `Automaton`
    """
    aut = copy.copy(aut)
    t, init, safety = bv.bitblast_table(aut.vars)
    aut.update('init', init)
    aut.update('action', safety)
    # conjoin to avoid it later over BDD nodes
    _conj_owner(aut, 'env', 'infix')
    _conj_owner(aut, 'sys', 'infix')
    a = Automaton()
    a.vars = t
    # TODO: replace GR(1) syntax check
    # spec.check_syntax()
    _bitblast_owner(aut, a, 'env', t)
    _bitblast_owner(aut, a, 'sys', t)
    return a


def _conj_owner(aut, owner, as_what):
    """Conjoin the lists in the attributes of `owner`.

    @param as_what: `'bdd' or 'prefix' or 'infix'`
    """
    # get
    init = aut.init[owner]
    action = aut.action[owner]
    # compute
    if as_what == 'prefix':
        init = syntax.conj_prefix(init)
        action = syntax.conj_prefix(action)
    elif as_what == 'infix':
        init = syntax.conj(init)
        action = syntax.conj(action)
    elif as_what == 'bdd':
        def f(x, y):
            return aut.bdd.apply('and', x, y)
        init = syntax.recurse_binary(f, init)
        action = syntax.recurse_binary(f, action)
    else:
        raise Exception(
            'unknown as_what="{s}"'.format(s=as_what))
    # set
    aut.init[owner] = [init]
    aut.action[owner] = [action]


def _bitblast_owner(aut, a, owner, t):
    """Bitblast init, action, win of `owner`."""
    def f(x):
        return bv.bitblast(x, t)
    assert owner in ('env', 'sys'), owner
    a.init[owner] = map(f, aut.init[owner])
    a.action[owner] = map(f, aut.action[owner])
    if owner == 'env':
        s = '<>[]'
    else:
        s = '[]<>'
    a.win[s] = map(f, aut.win[s])


# at least 4 use cases:
#
# 1. build `dd.bdd.BDD` from scratch (so levels too)
# 2. use a `dd.bdd.BDD` loaded from a `dddmp` file,
#    so extract the levels, because they exist already
# 3. build `dd.cudd.BDD` from scratch
#    (simplest if it tells you the indices)
# 4. use a `dd.cudd.BDD` that already exists,
#    e.g., add counters to build a transducer.
def _bitvector_to_bdd(aut, bdd=None, add=True):
    """Return `Automaton` with BDD formulae.

    @type aut: `Automaton`
    @type bdd: `dd.bdd.BDD`
    """
    dvars = aut.vars
    dbits = bv.list_bits(dvars)
    ubits = set(b for b, d in dbits.iteritems()
                if d['owner'] == 'env')
    # use fresh `BDD` ?
    if bdd is None:
        ordbits = _pick_var_order(dbits, ubits)
        order, prime, partition = _partition_vars(ordbits, ubits)
        bdd = aut.bdd
        for var, level in order.iteritems():
            bdd.add_var(var, level)
    else:
        # check no missing vars,
        # including primed
        pbits, _, _ = _partition_vars(dbits, ubits)
        bdd_bits = bdd.vars
        missing = set(pbits).difference(bdd_bits)
        if add:
            for bit in missing:
                logger.debug('add missing bit "{b}"'.format(b=bit))
                if bit.endswith("'"):
                    unprimed_bit = bit[:-1]
                else:
                    unprimed_bit = bit
                level = dbits[unprimed_bit].get('level')
                if level is None:
                    bdd.add_var(bit)
                else:
                    logger.debug('at level: {level}'.format(level=level))
                    try:
                        bdd.insert_var(bit, level)
                    except:
                        bdd.add_var(bit)
        else:
            assert not missing, (missing, pbits, bdd_bits)
        # extract order and partition
        prime, partition = _extract_partition(bdd.vars, ubits)
    # bundle as:
    a = Automaton()
    a.bdd = bdd
    # vars
    a.vars = copy.deepcopy(dvars)
    a.uvars = partition['uvars']
    a.upvars = partition['upvars']
    a.evars = partition['evars']
    a.epvars = partition['epvars']
    a.ubvars = set(a.uvars).union(a.upvars)
    a.ebvars = set(a.evars).union(a.epvars)
    a.uevars = set(a.uvars).union(a.evars)
    a.uepvars = set(a.upvars).union(a.epvars)
    # priming
    a.prime = prime
    a.unprime = {v: k for k, v in prime.iteritems()}
    # slugsin -> BDD
    # add long attributes first,
    # to improve  effectiveness of reordering.
    # better if each attr is one formula.
    from_sections = _make_section_map(aut)
    to_sections = _make_section_map(a)
    lengths = {
        k: _section_len(v)
        for k, v in from_sections.iteritems()}
    sort = sorted(
        from_sections,
        key=lengths.__getitem__,
        reverse=True)
    for section in sort:
        p = from_sections[section]
        q = to_sections[section]
        _to_bdd(p, q, bdd)
    return a


def _make_section_map(aut):
    """Return `dict` of `Automaton` attributes."""
    sections = dict(
        env_init=aut.init['env'],
        env_action=aut.action['env'],
        sys_init=aut.init['sys'],
        sys_action=aut.action['sys'])
    sections['<>[]'] = aut.win['<>[]']
    sections['[]<>'] = aut.win['[]<>']
    return sections


def _section_len(formulae):
    """Return sum of `len` of `str` in `formulae`."""
    return sum(len(s) for s in formulae)


def _to_bdd(a, b, bdd):
    """For each element of `a`, append a `bdd` node to `b`."""
    for s in a:
        u = _bdd.add_expr(s, bdd)
        b.append(u)


def _pick_var_order_eu(bits, ubits):
    ebits = set(bits).difference(ubits)
    u = natsort.natsorted(ubits)
    e = natsort.natsorted(ebits)
    return e + u


def _pick_var_order(bits, ubits):
    """Sort the `bits` in natural order.

    Two separate orders are constructed:

        - for `ubits`
        - for the rest of `bits`

    and concatenated in that order.
    """
    array_bits = {b for b, d in bits.iteritems() if d.get('array')}
    other = set(bits).difference(array_bits)
    top = natsort.natsorted(other)
    bottom = natsort.natsorted(array_bits)
    r = top + bottom
    return r


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
        logger.debug('{var} at {j}, {pvar} at {jp}'.format(
            var=var, pvar=primed, j=j, jp=j + 1))
        d[var] = j
        d[primed] = j + 1
        prime[var] = primed
    evars = {var for var in ordvars if var not in uvars}
    upvars = map(prime.get, uvars)
    epvars = map(prime.get, evars)
    # bundle
    c = [uvars, upvars, evars, epvars]
    uvars, upvars, evars, epvars = map(set, c)
    partition = dict(uvars=uvars, upvars=upvars,
                     evars=evars, epvars=epvars)
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
        if dtype in ('int', 'saturating'):
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

    @param dbits: `BDD.vars` that maps each bit to an identifier.
        The identifier may be its name, level, or index.
        It depends on how quantification works for the manager used.
    @type dbits: `dict`
    @param ubits: universally quantified unprimed bits
    @type ubits: `set`

    @return: priming and partition, containing levels
    @rtype: `tuple(dict, dict)`
    """
    suffix = "'"
    diff = set(ubits).difference(dbits)
    assert not diff, (diff, ubits, dbits)
    uvars = set()
    upvars = set()
    evars = set()
    epvars = set()
    for bit in dbits:
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
        prime[bit] = pbit
    partition = dict(uvars=uvars, upvars=upvars,
                     evars=evars, epvars=epvars)
    return prime, partition


def assert_primed_adjacent(prime, bdd):
    """Raise `AssertionError` if not neighbors.

    @param prime: map each unprimed to a primed var.
    @type prime: `dict(str: str)`
    @type bdd: `BDD`
    """
    # check adjacency of unprimed-primed pairs
    for x, y in prime.iteritems():
        i = bdd.level_of_var(x)
        j = bdd.level_of_var(y)
        assert abs(i - j) == 1, (
            'Variables "{x}" (level {i}) and '
            '"{y}" (level {j}) are not adjacent.\n'
            'Primed and unprimed vars must be adjacent in '
            'the given BDD.').format(x=x, y=y, i=i, j=j)


def _join(c):
    """Return `str` with one element of `c` per line."""
    return '\n'.join(str(x) for x in c)
