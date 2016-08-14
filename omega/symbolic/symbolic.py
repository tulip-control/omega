"""Symbolic automaton.

Including bitblasting of first-order to bitvector logic,
and transformation to BDD nodes.
"""
import copy
import logging
import pprint

import dd.bdd
import natsort

from omega.logic import bitvector as bv
from omega.logic import syntax as stx
from omega.symbolic import bdd as sym_bdd


logger = logging.getLogger(__name__)


class Automaton(object):
    r"""Transition relation, initial condition, and hidden variables.

    User-defined attributes
    =======================

    You define the attributes:

      - vars: `dict` that maps each variable name to
        a `dict` with keys:

          - `"type": "bool" or "modwrap" or "saturating"`
          - `"dom": (min, max)`, range of integer
          - `"owner": "env" or "sys"`
          - `"init"`: has suitable `__str__` (and is optional)

      - init: initial condition
      - action: transition relation
      - win: winning condition
      - acceptance: `str` that describes `win`,
          for example `'Streett(1)'`
      - moore: choose between Moore or Mealy implementation
      - plus_one: strict implication with `\weakprevious`
      - qinit: quantification of initial variable values:

        - `'\A \A'`
        - `'\A \E'`
        - `'\E \A'`
        - `'\E \E'`

    Each of `init, action` is a `dict`:

      `{player: list(), ...}`

    `win` is a `dict` of the form:

      `{'<>[]': list(),
        '[]<>': list()}`

    Add formulae (as strings) to these lists.
    Call the method `build` to convert these formulae to BDD nodes,
    and generate the below.


    Auto-generated attributes
    =========================

    The method `build` adds to `vars[var]` the keys:

      - `"bitnames"`: `list`
      - `"signed"`: `True` if signed integer
      - `"width"`: `len(bitnames)`

    Each of the following is a `set` of variable names:

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


    References
    ==========

    Leslie Lamport
        "The temporal logic of actions"
        ACM Transactions on Programming
        Languages and Systems (TOPLAS),
        Vol.16, No.3, pp.872--923, 1994

    Rajeev Alur, Thomas A. Henzinger, Orna Kupferman
        "Alternating-time temporal logic"
        Journal of the ACM (JACM)
        Vol.49, No.5, pp.672--713, 2002

    Klaus Schneider
        "Verification of reactive systems"
        Springer, 2004
    """

    def __init__(self):
        self.players = {'env': 0, 'sys': 1}  # name -> turn
        self.vars = dict()
        self.moore = True
        self.plus_one = True
        self.qinit = '\A \A'
        # formulae
        self.init = dict(env=list(), sys=list())
        self.action = dict(env=list(), sys=list())
        self.win = {'<>[]': list(), '[]<>': list()}
        self.acceptance = 'Streett(1)'
        # auto-populated
        self.turns = list()  # inverse of `self.players`
        # subsets of bits
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
        self.prime = dict()  # unprimed -> primed
        self.unprime = dict()  # primed -> unprimed
        # aux
        # init only to aid static analysis
        self.bdd = dd.bdd.BDD()

    def __copy__(self):
        a = Automaton()
        a.players = copy.deepcopy(self.players)
        a.vars = copy.deepcopy(self.vars)
        a.init = copy.deepcopy(self.init)
        a.action = copy.deepcopy(self.action)
        a.win = copy.deepcopy(self.win)
        a.acceptance = self.acceptance
        a.bdd = self.bdd
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
            '',
            'Moore' if self.moore else 'Mealy',
            ('causal' if self.plus_one else
            'circular') + ' implication',
            '',
            'Initially:',
            self.qinit]
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
        d = dict(
            vars=self.vars,
            init=self.init,
            action=self.action,
            win=self.win,
            acceptance=self.acceptance,
            moore=self.moore,
            plus_one=self.plus_one,
            qinit=self.qinit)
        return repr(d)

    def build(self):
        """Return `Automaton` with formulae as BDD nodes.

        Bitblast variables and formulae,
        add bits to `self.bdd`,
        and populate primed and unprimed bits.

        BDD levels defined only if no existing bits.
        Otherwise, reorder to desired order later.
        """
        aut = _bitblast(self)
        aut.bdd = self.bdd
        aut = _bitvector_to_bdd(aut)
        aut.moore = self.moore
        aut.plus_one = self.plus_one
        aut.qinit = self.qinit
        return aut

    def assert_consistent(self, built=False):
        """Raise `AssertionError` if not well-formed.

        @param built: if `True`,
        then assert `build` has been called.
        """
        # check attributes
        for d in (self.init, self.action, self.win):
            for k, v in d.iteritems():
                for u in v:
                    if built:
                        try:
                            assert u in self.bdd, u
                        except TypeError:
                            raise AssertionError(
                                'Automaton needs '
                                'to be compiled')
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
        u = sym_bdd.add_expr(s, self.bdd)
        return u


def fill_blanks(aut, as_bdd=False, rabin=False):
    """Add `"True"` to empty attributes `init`, `action`, `win`.

    @param as_bdd: if `True`, then represent `"True"` as `1`
    """
    if as_bdd:
        true = aut.bdd.true
        false = aut.bdd.false
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
    players = dict(aut.players)
    aut = copy.copy(aut)
    t = bv.bitblast_table(aut.vars)
    init, action = bv.type_invariants(t)
    for var, c in init.iteritems():
        owner = aut.vars[var]['owner']
        # collect type invariants of parameters too,
        # for convenience later
        aut.init.setdefault(owner, list())
        aut.init[owner].extend(c)
    for var, c in action.iteritems():
        owner = aut.vars[var]['owner']
        aut.action.setdefault(owner, list())
        aut.action[owner].extend(c)
    # conjoin to avoid it later over BDD nodes
    _conj_owner(aut, 'env', 'infix')
    _conj_owner(aut, 'sys', 'infix')
    a = Automaton()
    a.players = players
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
        init = stx.conj_prefix(init)
        action = stx.conj_prefix(action)
    elif as_what == 'infix':
        init = stx.conj(init)
        action = stx.conj(action)
    elif as_what == 'bdd':
        def f(x, y):
            return aut.bdd.apply('and', x, y)
        init = stx.recurse_binary(f, init)
        action = stx.recurse_binary(f, action)
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


def _bitvector_to_bdd(aut):
    """Return `Automaton` with BDD formulae.

    @type aut: `Automaton`
    """
    players = dict(aut.players)
    table = aut.vars
    bits = bv.bit_table(table, table)
    # index both, to allow for unquantified parameters
    ubits = set(b for b, d in bits.iteritems()
                if d['owner'] == 'env')
    ebits = set(b for b, d in bits.iteritems()
                if d['owner'] == 'sys')
    b = _pick_var_order(bits, ubits)
    b = _add_primed_bits(b)
    bdd = aut.bdd
    # define levels only if no existing vars
    if bdd.vars:
        for var in b:
            bdd.add_var(var)
    else:
        for level, var in enumerate(b):
            bdd.add_var(var, level)
    # bundle as:
    a = Automaton()
    a.vars = copy.deepcopy(table)
    a.players = players
    a.bdd = bdd
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
    # vars
    player_vars = {k for k, d in table.iteritems()
                   if d['owner'] in players}
    if not player_vars:
        print('Warning: no player variables.')
        return a
    bits = bv.bit_table(player_vars, table)
    prime, partition = _partition_vars(bits, ubits, ebits)
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
        u = sym_bdd.add_expr(s, bdd)
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


def _add_primed_bits(unprimed_bits):
    """Return list of ordered primed and unprimed bits."""
    bits = list()
    for bit in unprimed_bits:
        primed = stx.prime(bit)
        bits.append(bit)
        bits.append(primed)
    return bits


def _partition_vars(bits, ubits, ebits):
    """Return primed and unprimed variable names.

    @param bits: `list` of variable names as `str`
    @param ubits: universally quantified variables
    @param ebits: existentially quantified variables

    @return: (prime, partition)
      - prime: `dict` that maps unprimed to primed variable names
      - partition: `dict(uvars=set, upvars=set,
                         evars=set, epvars=set)`
    """
    prime = {b: stx.prime(b) for b in bits}
    partition = dict(
        uvars=set(ubits),
        upvars={prime[b] for b in ubits},
        evars=set(ebits),
        epvars={prime[b] for b in ebits})
    return prime, partition


def _prime_and_order_table(t):
    """Return ordered table of primed and unprimed variables.

    The table maps each (integer or Boolean) variable to
    a `dict` of attributes (same as `t`).
    The attributes include `"bitnames"`.

    The following attributes are added:

      - level: index among ordered prime and unprimed integers
      - len: number of values the variable can take

    @param t: table of unprimed variables as `str`
    @type t: `dict`

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
        primed = stx.prime(var)
        pbits = [stx.prime(bit) for bit in bits]
        k = j + 1
        # copy attr
        dvars[var] = dict(d)
        dvars[primed] = dict(d)
        # update attr
        dvars[var].update(level=j, len=m, bitnames=bits)
        dvars[primed].update(level=k, len=m, bitnames=pbits)
    return dvars


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


def _assert_support_moore(aut):
    """Raise `AssertionError` if Moore that depends on `env'`."""
    if not aut.moore:
        return
    (u,) = aut.action['sys']
    s = aut.bdd.support(u)
    upvars_in_support = s.intersection(aut.upvars)
    assert not upvars_in_support, upvars_in_support


def _join(c):
    """Return `str` with one element of `c` per line."""
    return '\n'.join(str(x) for x in c)
