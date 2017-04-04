"""First-order wrapper for BDDs.

References
==========

Leslie Lamport, Lawrence C. Paulson
    "Should your specification language be typed?"
    ACM Transactions on Programming Languages and Systems
    Vol.21, No.3, pp.502--526, 1999

Kenneth Kunen
    "The foundations of mathematics"
    College Publications, 2009
"""
# Copyright 2016 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
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
    from dd import autoref as _bdd

from omega.logic import bitvector as bv
from omega.logic import lexyacc
from omega.logic import syntax as stx
from omega.symbolic import bdd as sym_bdd
from omega.symbolic import cover as cov
from omega.symbolic import enumeration as enum


log = logging.getLogger(__name__)
_parser = lexyacc.Parser()
TYPE_HINTS = {'int', 'saturating', 'modwrap'}


class Context(object):
    """First-order interface to a binary decision diagram.

    All operations assume that integer-valued variables
    take only values that correspond to the Boolean-valued
    variables that refine them.

    Quantification is implicitly bounded.
    In the future, the bound will be made explicit
    in the syntax.

    "Context" alludes to extension of a formal theory
    by definitions [Kunen, Sec.II.15].
    """

    def __init__(self):
        """Instantiate first-order context."""
        self.vars = dict()
        self.bdd = _bdd.BDD()
        self.op = dict()  # namespace of operators
        self.op_bdd = dict()

    def __str__(self):
        return ((
            'Refinement of variables by '
            'Boolean-valued variables:\n\n'
            '{vars}').format(
                vars=pprint.pformat(self.vars)))

    def declare(self, **vrs):
        """Declare variable identifiers given as keyword args.

        Example:

        ```python
        c.declare(x=(2, 15), y='bool', z=(-3, 4))
        ```

        Wrapper of `self.add_vars` that may replace it.
        """
        d = bv.make_symbol_table(vrs)
        self.add_vars(d)

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
        assert dvars, dvars
        self._avoid_redeclaration(dvars)
        vrs = {k: v for k, v in dvars.items()
               if k not in self.vars}
        if not vrs:
            return
        t = bv.bitblast_table(vrs)
        self.vars.update(t)
        bits = bv.bit_table(t, t)
        for bit in bits:
            self.bdd.add_var(bit)

    def _avoid_redeclaration(self, dvars):
        # if any `dvars` not fresh, then must be same
        gen = (var for var in dvars if var in self.vars)
        for var in gen:
            old = self.vars[var]
            for k, v in dvars[var].items():
                if k in old and v == old[k]:
                    continue
                raise ValueError((
                    'attempted to redeclare "{var}" '
                    'where old: {old} and new: {new}').format(
                        var=var, old=old, new=dvars[var]))

    def support(self, u):
        """Return FOL variables that `u` depends on."""
        supp = self.bdd.support(u)
        bit2int = bv.map_bits_to_integers(self.vars)
        return set(map(bit2int.__getitem__, supp))

    def let(self, defs, u):
        """Return substitution using `defs` in `u`.

        @param defs: `dict` that maps variable names to BDD operators
            or values.
        @param u: BDD operator
        @return: BDD operator
        """
        return self.replace(u, defs)

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

    def count(self, u, care_vars=None):
        """Return number of satisfying assignments.

        @param care_vars: variables that the assignments
            should contain. Should be `support(u) <= care_vars`
            If `care_vars == None`, then use `support(u)`.
        """
        # We could allow `support(u) > care_vars`.
        # But that needs a dedicated BDD traversal
        # (to avoid enumeration). Deferred until needed.
        support = self.support(u)
        if care_vars is None:
            care_vars = support
        assert set(care_vars) >= support, (care_vars, support)
        bits = _refine_vars(care_vars, self.vars)
        n = len(bits)
        c = self.bdd.sat_len(u, n)
        assert c == int(c), c
        assert c >= 0, c
        return c

    def pick(self, u, care_vars=None):
        """Return a satisfying assignment, or `None`."""
        return next(self.pick_iter(u, care_vars), None)

    def pick_iter(self, u, care_vars=None):
        """Generator of first-order satisfying assignments."""
        if care_vars is None:
            care_bits = None
        elif care_vars:
            care_bits = bv.bit_table(care_vars, self.vars)
        else:
            care_bits = set()
        for bit_assignment in self.bdd.sat_iter(
                u, care_bits=care_bits):
            for d in enum._bitfields_to_int_iter(
                    bit_assignment, self.vars):
                yield d

    def define(self, e):
        """Register operator definitions.

        The string `e` must contain definitions. Example:

        ```python
        e = '''
            a == x + y > 3
            b == z - x <= 0
            c == a /\ b
            '''
        ```

        In the future, this method may merge with `add_expr`.
        """
        assert stx.isinstance_str(e), e
        bv_defs = bv._parser.parse(e)
        defs = _parser.parse(e)
        for opdef, bv_opdef in zip(defs, bv_defs):
            assert opdef.operator == '==', opdef
            name_ast, expr_ast = opdef.operands
            _, bv_ast = bv_opdef.operands
            name = name_ast.value
            if name in self.vars:
                raise ValueError((
                    'Attempted to define operator "{name}", '
                    'but "{name}" already declared as variable: '
                    '{old}').format(
                        name=name, old=self.vars[name]))
            if name in self.op:
                raise ValueError((
                    'Attempted to redefine operator "{name}". '
                    'Previous definition as: "{old}"').format(
                        name=name, old=self.op[name]))
            s = bv_ast.flatten(
                t=self.vars, defs=self.op_bdd)
            assert stx.isinstance_str(s), s
            # sensitive point:
            #     operator expressions are stored before substitutions
            #     operator BDDs are stored after operator substitutions
            # operator definitions cannot change, so this should
            # not cause problems as currently arranged.
            self.op[name] = expr_ast.flatten()
            self.op_bdd[name] = sym_bdd.add_expr(s, self.bdd)

    def add_expr(self, e, with_ops=False):
        """Add first-order predicate.

        A predicate is a Boolean-valued formula.
        """
        assert stx.isinstance_str(e), e
        # optional because current implementation is slow
        if with_ops:
            defs = self.op
        else:
            defs = None
        s = bv.bitblast(e, vrs=self.vars, defs=defs)
        assert stx.isinstance_str(s), s  # was `e` a predicate ?
        return sym_bdd.add_expr(s, self.bdd)

    def to_expr(self, u, care=None, **kw):
        """Return minimal DNF of integer inequalities.

        For now, this method supports all variables in
        `support(u)` being integers.

        @param care: BDD of care set
        @param kw: keyword args are passed to
            function `cover.dumps_cover`.
        """
        if care is None:
            care = self.bdd.true
        cover = cov.minimize(u, care, self)
        s = cov.dumps_cover(
            cover, u, care, self, **kw)
        # prepare to assert
        _, px, _, _ = cov._setup_aux_vars(u, care, self)
        r = cov._list_orthotope_expr(
            cover, px, self, simple=True)
        r = stx.disj(r)
        u_ = self.add_expr(r)
        # promise to match `u` only inside `care`
        # forgive `|#  u => care`
        assert u & care == u_ & care, s
        return s

    def assign_from(self, assignment):
        """Return bdd from `assignment` to variables.

        @param assignment: `dict` that maps each variable to
            a value (`int` or `bool`) in accord with `self.vars`.
        """
        bit_values = _refine_assignment(assignment, self.vars)
        return self.bdd.cube(bit_values)

    def apply(self, op, u, v=None, w=None):
        """Apply operator `op` on operands `u, v, w`."""
        return self.bdd.apply(op, u, v, w)

    @property
    def false(self):
        """Return `self.bdd.false`."""
        return self.bdd.false

    @property
    def true(self):
        """Return `self.bdd.true`."""
        return self.bdd.true


def reorder(dvars, fol):
    """Shift integers up in the variable order of `fol.bdd`."""
    assert dvars, dvars
    bdd = fol.bdd
    for var, d in dvars.items():
        level = d['level']
        dv = fol.vars[var]
        var_type = dv['type']
        if var_type == 'bool':
            bitnames = [var]
        else:
            assert var_type in TYPE_HINTS, var_type
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
                 for i in range(len(bdd.vars))]
        below = order[:level]
        above = order[level:]
        above = [v for v in above if v not in bitnames]
        new_order = below + bitnames + above
        dorder = {var: i for i, var in enumerate(new_order)}
        _bdd.reorder(bdd, dorder)
        order = [bdd.var_at_level(i)
                 for i in range(len(bdd.vars))]
        assert order == new_order, (order, new_order)


def _refine_vars(fol_vars, table):
    """Return bits that represent the `fol_vars`."""
    if fol_vars:
        bits = bv.bit_table(fol_vars, table)
    else:
        # `bit_table` raises `AssertionError` for
        # empty `fol_vars`
        bits = set()
    return bits


def _refine_assignment(m, table):
    """Return bit assignment, from int/bool assignment `m`."""
    bit_values = dict()
    for var, value in m.items():
        assert var in table, var
        if table[var]['type'] == 'bool':
            bit_values[var] = value
            continue
        d = _int_to_bit_assignment(var, value, table)
        bit_values.update(d)
    return bit_values


def _int_to_bit_assignment(var, value, table):
    """Return assignment to bits from assignment to integer.

    Skips the parser, compared to `_assignment_to_bdd`.
    """
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


def _assignment_to_bdd(dvars, fol):
    """Return BDD from assignment to `dvars`.

    Handles only assignments of integer values.
    """
    raise DeprecationWarning('use `_refine_assignment` instead')
    conj = stx.conj(
        '{var} = {value}'.format(var=var, value=value)
        for var, value in dvars.items())
    u = fol.add_expr(conj)
    return u


def _refine_renaming(fol_rename, table):
    """Return renaming of bits, from renaming of FOL vars."""
    bit_rename = dict()
    for old, new in fol_rename.items():
        old_d = table[old]
        new_d = table[new]
        old_type = old_d['type']
        new_type = new_d['type']
        assert old_type == new_type, (old_type, new_type)
        if old_type == 'bool':
            bit_rename[old] = new
            continue
        assert old_type in TYPE_HINTS, old_type
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


class Operator(_bdd.Function):
    """Predicate over first-order variables.

    Represented using a binary-decision diagram.
    Pass the relevant `Context` upon instantiation:

    ```python
    c = Context()
    v = Operator(u, c)
    ```
    """

    def __init__(self, *arg, **kw):
        self.fol = kw.pop('fol')
        super(Operator, self).__init__(*arg, **kw)

    @property
    def support(self):
        return self.fol.support(self.node)


def _prime_bits_of_integers(ints, t):
    """Return bit priming for integers in `x`."""
    bit_rename = dict()
    for i in ints:
        bits = t.vars[i]['bitnames']
        d = {k: stx.prime(k) for k in bits}
        bit_rename.update(d)
    return bit_rename


def closed_interval(var, a, b):
    """Return string `a <= var <= b`."""
    return (
        '({a} <= {var}) & '
        '({var} <= {b})').format(
            var=var, a=a, b=b)


def add_one_hot(var, a, b):
    """Return symbol table for one-hot encoding."""
    t = dict()
    for i in range(a, b):
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
