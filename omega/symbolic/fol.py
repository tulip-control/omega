"""First-order wrapper for BDDs.

References
==========

Leslie Lamport, Lawrence C. Paulson
    "Should your specification language be typed?"
    ACM Transactions on Programming Languages and Systems
    Vol.21, No.3, pp.502--526, 1999
"""
# other places where relevant functions exist:
#   dd.mdd
#   omega.logic.bitvector
#   omega.symbolic.enumeration
#
# examples/interleaving
# symbolic_transducers
# simulate
import logging
import pprint

try:
    from dd import cudd as _bdd
except ImportError:
    from dd import bdd as _bdd

from omega.logic import bitvector as bv
from omega.logic import syntax as stx
from omega.symbolic import bdd as sym_bdd
from omega.symbolic import enumeration as enum


log = logging.getLogger(__name__)


class Context(object):
    """First-order interface to a binary decision diagram.

    All operations assume that integer-valued variables
    take only values that correspond to the Boolean-valued
    variables that refine them.

    Quantification is implicitly bounded.
    In the future, the bound will be made explicit
    in the syntax.
    """

    def __init__(self):
        """Instantiate first-order context."""
        self.vars = dict()
        self.bdd = _bdd.BDD()

    def __str__(self):
        return ((
            'Refinement of variables by '
            'Boolean-valued variables:\n\n'
            '{vars}').format(
                vars=pprint.pformat(self.vars)))

    def add_vars(self, dvars):
        r"""Refine variables in `dvars`.

        The variables in `dvars` should have type hints.
        A Boolean-valued variable remains so.
        An integer-valued variable is assumed to take the
        value resulting as a function of some (fresh)
        Boolean-valued variables.

        Sometimes these variables are called "bits".
        The function is based on two's complement,
        see `omega.logic.bitvector` for details.

        In other words, type hints are used to pick
        a refinement of integers by finitely many bits.
        A sufficient number of bits is selected,
        and operations assume this as type invariant,
        *not* the exact type hint given.

        For example, an integer `x` with type hint `x \in 0..2`
        will be refined using 2 Boolean-valued variables
        `x_0` and `x_1`. All operations and quantification
        will assume that `x \in 0..3`.
        Mind the extra value (3) allowed,
        compared to the hint (0..2).

        Attention:

        - Fine-grained type predicates
          (`n..m` with `n` and `m` other than powers of 2)
          are not managed here.

        - Priming is not reasoned about here.
          Priming is cared for by other modules.
        """
        # if any `dvars` not fresh, then must be same
        assert dvars, dvars
        common = set(dvars).intersection(self.vars)
        for var in common:
            for k, v in dvars[var].iteritems():
                assert self.vars[var][k] == v
        if common:
            log.warning('attempted adding existing vars')
        dvars = {k: v for k, v in dvars.iteritems()
                 if k not in common}
        if not dvars:
            return
        common = set(dvars).intersection(self.vars)
        assert not common, common
        t = bv.bitblast_table(dvars)
        self.vars.update(t)
        bits = bv.bit_table(t, t)
        for bit in bits:
            self.bdd.add_var(bit)

    def support(self, u):
        """Return FOL variables that `u` depends on."""
        supp = self.bdd.support(u)
        bit2int = bv.map_bits_to_integers(self.vars)
        return set(map(bit2int.__getitem__, supp))

    def replace(self, u, vars_to_new):
        """Return substitution of var names by values or vars.

        @param vars_to_new: `dict` that maps each var name to
            a var (as `str`), or to a value (as `bool` or `int`).
        """
        if not vars_to_new:
            return u
        assert vars_to_new, vars_to_new
        for k in vars_to_new:
            rename = stx.isinstance_str(vars_to_new[k])
            break
        if rename:
            bit_rename = _refine_renaming(vars_to_new, self.vars)
            return self.bdd.rename(u, bit_rename)
        else:
            bit_values = _refine_assignment(vars_to_new, self.vars)
            return self.bdd.cofactor(u, bit_values)

    def replace_with_bdd(self, u, var_subs):
        """Substitute Boolean-valued variables with BDD nodes."""
        # distinct from `replace` due to restriction to Boolean
        return self.bdd.compose(u, var_subs)

    def forall(self, qvars, u):
        """Universally quantify `qvars` in `u`."""
        r = self.apply('not', u)
        r = self.exist(qvars, r)
        r = self.apply('not', r)
        return r

    def exist(self, qvars, u):
        """Existentially quantify `qvars` in `u`."""
        if not qvars:
            return u
        qbits = bv.bit_table(qvars, self.vars)
        return self.bdd.exist(qbits, u)

    def pick(self, u, full, care_vars):
        """Return a satisfying assignment, or `None`."""
        try:
            return next(self.pick_iter(u, full, care_vars))
        except StopIteration:
            return None

    def pick_iter(self, u, full, care_vars):
        """Return generator of first-order satisfying assignments."""
        if care_vars:
            care_bits = bv.bit_table(care_vars, self.vars)
        else:
            care_bits = set()
        for bit_assignment in self.bdd.sat_iter(
                u, full=full, care_bits=care_bits):
            d = next(enum._bitfields_to_int_iter(
                bit_assignment, self.vars))
            yield d

    def add_expr(self, e):
        """Add first-order predicate.

        A predicate is a Boolean-valued formula.
        """
        assert stx.isinstance_str(e), e
        s = bv.bitblast(e, self.vars)
        assert stx.isinstance_str(s), s  # was `e` a predicate ?
        return sym_bdd.add_expr(s, self.bdd)

    def apply(self, op, u, v=None, w=None):
        """Apply operator `op` on operands `u, v, w`."""
        return self.bdd.apply(op, u, v, w)


def reorder(dvars, fol):
    """Shift integers up in the variable order of `fol.bdd`."""
    assert dvars, dvars
    bdd = fol.bdd
    for var, d in dvars.iteritems():
        level = d['level']
        dv = fol.vars[var]
        var_type = dv['type']
        if var_type == 'bool':
            bitnames = [var]
        else:
            assert var_type in ('int', 'saturating', 'modwrap')
            bitnames = dv['bitnames']
        # print('Shifting bits {bitnames} to '
        #       'level {level}'.format(
        #         level=level,
        #         bitnames=bitnames))
        # assert each bit goes up in level
        for bit in bitnames:
            old_level = bdd.level_of_var(bit)
            assert old_level >= level, (old_level, level)
        # shift to levels wanted
        order = [bdd.var_at_level(i)
                 for i in xrange(len(bdd.vars))]
        below = order[:level]
        above = order[level:]
        above = [v for v in above if v not in bitnames]
        new_order = below + bitnames + above
        dorder = {var: i for i, var in enumerate(new_order)}
        _bdd.reorder(bdd, dorder)
        order = [bdd.var_at_level(i)
                 for i in xrange(len(bdd.vars))]
        assert order == new_order, (order, new_order)


def _refine_assignment(fol_values, table):
    """Return assignment to bits, from FOL assignment."""
    bit_values = dict()
    for var, value in fol_values.iteritems():
        assert var in table, var
        if table[var]['type'] == 'bool':
            bit_values[var] = value
            continue
        d = _int_to_bit_assignment(var, value, table)
        bit_values.update(d)
    return bit_values


def _refine_renaming(fol_rename, table):
    """Return renaming of bits, from renaming of FOL vars."""
    bit_rename = dict()
    for old, new in fol_rename.iteritems():
        old_d = table[old]
        new_d = table[new]
        old_type = old_d['type']
        new_type = new_d['type']
        assert old_type == new_type, (old_type, new_type)
        if old_type == 'bool':
            bit_rename[old] = new
            continue
        assert old_type in ('int', 'saturating', 'modwrap')
        # int
        old_dom = old_d['dom']
        new_dom = new_d['dom']
        assert old_dom == new_dom, (old_dom, new_dom)
        old_bits = old_d['bitnames']
        new_bits = new_d['bitnames']
        assert len(old_bits) == len(new_bits), (
            old_bits, new_bits)
        # no overlap (otherwise use `compose`)
        common = set(old_bits).intersection(new_bits)
        assert not common, (
            common, old_bits, new_bits)
        # bit substitution
        # assume same bit numbering (index 0 is LSB)
        bit_rename.update(zip(old_bits, new_bits))
    return bit_rename


def _int_to_bit_assignment(var, value, table):
    """Return assignment to bits from assignment to integer."""
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
    return values


def _prime_bits_of_integers(ints, t):
    """Return bit priming for integers in `x`."""
    bit_rename = dict()
    for i in ints:
        bits = t.vars[i]['bitnames']
        d = {k: stx.prime(k) for k in bits}
        bit_rename.update(d)
    return bit_rename


def _assignment_to_bdd(dvars, fol):
    """Return BDD from assignment to `dvars`."""
    conj = stx.conj(
        '{var} = {value}'.format(var=var, value=value)
        for var, value in dvars.iteritems())
    u = fol.add_expr(conj)
    return u


def closed_interval(var, a, b):
    """Return string `a <= var <= b`."""
    return (
        '({a} <= {var}) & '
        '({var} <= {b})').format(
            var=var, a=a, b=b)


def add_one_hot(var, a, b):
    """Return symbol table for one-hot encoding."""
    t = dict()
    for i in xrange(a, b):
        var = '{var}{i}'.format(var=var, i=i)
        d = dict(type='bool', owner='parameters', level=0)
        t[var] = d
    return t


def array_to_logic(a, counter, aut):
    """Return logic formula for Boolean array `a`.

    No array bounds produced.
    Instead, if `(counter < 0) or (counter >= len(a) - 1)`,
    then select `a[-1]`.
    Therefore, array bounds *must* be added separately.

    @param a: `list` of elements
    @param counter: name of index variable
    """
    bdd = aut.bdd
    r = a[-1]
    for i, x in enumerate(a[:-1]):
        s = '{counter} = {i}'.format(counter=counter, i=i)
        u = aut.add_expr(s)
        r = bdd.ite(u, x, r)
    return r


def multiplexer(a, bits, aut):
    """Return BDD node for selection of elements from `a`.

    The resulting expression is:

    ```
    ite(bits[-1], a[-1],
        ite(bits[-2], a[-2],
            ...
            ite(bits[1], a[1],
                ite(bits[0], a[0], FALSE)
    ```

    This shows that if i < j,
    then b[i] has lower priority than b[j].
    So, this is not exactly a multiplexer.
    """
    assert len(a) == len(bits), (a, bits)
    bdd = aut.bdd
    r = bdd.false
    for bit, x in zip(bits, a):
        g = aut.add_expr(bit)
        r = bdd.ite(g, x, r)
    return r
