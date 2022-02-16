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
# All rights reserved. Licensed under 3-clause BSD.
#
# other places where relevant functions exist:
#   `dd.mdd`
#   `omega.logic.bitvector`
#   `omega.symbolic.enumeration`
#
# `examples/interleaving`
# `symbolic_transducers`
# `simulate`
import logging
import pprint

try:
    import dd.cudd as _bdd
except ImportError:
    import dd.autoref as _bdd

import omega.logic.bitvector as bv
import omega.logic.lexyacc as _lexyacc
import omega.logic.syntax as stx
import omega.symbolic.bdd as sym_bdd
import omega.symbolic.cover as cov
import omega.symbolic.enumeration as enum
import omega.symbolic.orthotopes as lat


log = logging.getLogger(__name__)
_parser = _lexyacc.Parser()
TYPE_HINTS = {'int', 'saturating', 'modwrap'}


class Context:
    """First-order interface to a binary decision diagram.

    All operations assume that integer-valued variables
    take only values that correspond to the Boolean-valued
    variables that refine them.

    Quantification is implicitly bounded.
    In the future, the bound will be made explicit
    in the syntax.

    "Context" alludes to extension of a formal theory
    by definitions [Kunen, Sec.II.15].

    The attributes of this class are considered to
    be internal.

    Attributes:

    - `vars`: mapping from variable names to
      useful information about what values are
      represented for the variable

    - `bdd`: `dd.autoref.BDD` or `dd.cudd.BDD`,
      depending on whether the Cython module `dd.cudd`
      is installed.

    You can assign to the attribute `Context.bdd`,
    but that assignment must happen immediately
    after instantiating the `Context` object,
    before the context is used in any way.

    The assignment must be an object of the
    type `dd.autoref.BDD`, `dd.cudd.BDD`,
    or any other type that has the same interface
    (e.g., methods) as these classes.
    """

    def __init__(self):
        """Instantiate first-order context."""
        self.vars = dict()
        self.bdd = _bdd.BDD()
        self.op = dict()  # operator name -> `str`
        self.op_bdd = dict()  # operator name -> bdd

    def __str__(self):
        """Return `str` description of `self`."""
        return (
            'Refinement of variables by '
            'Boolean-valued variables:\n\n'
            f'{pprint.pformat(self.vars)}')

    def declare(self, **vrs):
        r"""Declare variable identifiers.

        The variable identifiers are given as
        keyword parameters, and the corresponding
        keyword arguments are the type hints for
        those variables.

        Example:

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        ctx.declare(
            x=(2, 15),
            y='bool',
            z=(-3, 4))

        # create a BDD over the declared variables
        u = ctx.add_expr(r' (x <= 4) /\ y /\ (z = -2) ')
        print(u)
        ```

        Wrapper of `Context.add_vars()`.

        @param vrs:
            `dict` that maps each variable name
            to a type hint. A type hint is either:
            - the string `'bool'`, or
            - a pair of `int` (intended min and max values
              to represent: the actual range can be larger,
              because the representation of integer values
              is in two's complement
        @type vrs:
            `dict` with `str` keys,
            read above for value types
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

        For example, an integer `x` with
        type hint `x \in 0..2`
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

        The method `add_vars()` adds to
        `vars[var]` the keys:

          - `"bitnames"`: `list`
          - `"signed"`: `True` if signed integer
          - `"width"`: `len(bitnames)`

        `add_vars()` is considered internal.
        The interface is `Context.declare()`.
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
        """Raise `ValueError` if types would change."""
        # if any `dvars` not fresh, then must be same
        gen = (var for var in dvars if var in self.vars)
        for var in gen:
            old = self.vars[var]
            for k, v in dvars[var].items():
                if k in old and v == old[k]:
                    continue
                raise ValueError(
                    f'attempted to redeclare "{var}" '
                    f'where old: {old} and '
                    f'new: {dvars[var]}')

    def support(self, u):
        r"""Return FOL variables that `u` depends on.

        For example:

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        ctx.declare(
            x='bool',
            y=(0, 5))
        u = ctx.add_expr(
            r' x /\ (y = 5) ')
        support = ctx.support(u)
        assert support == {'x', 'y'}

        # BEWARE
        support_bits = ctx.bdd.support(u)
        assert support_bits == {'x', 'y_0', 'y_1', 'y_2'}

        support_bits = u.support
        assert support_bits == {'x', 'y_0', 'y_1', 'y_2'}
        ```

        The names of bits (`'y_0', 'y_1'` etc) are
        considered an implementation detail,
        and may change.

        Compare with `self.bdd.support()`,
        which returns bits.

        @param u:
            reference to root of BDD,
        @type u:
            `dd.autoref.Function` or
            `dd.cudd.Function`,
            must be the root of a BDD in `self.bdd`
        @return:
            set of variable names
        @type:
            `set` of `str`
        """
        supp = self.bdd.support(u)
        bit2int = bv.map_bits_to_integers(self.vars)
        return set(map(bit2int.__getitem__, supp))

    def let(self, defs, u):
        r"""Substitute variables in `u`.

        This method performs substitution in the
        way that `LET` expressions work:

        ```tla
        LET
            x == 1
            y == TRUE
        IN
            (x = 2) \/ y
        ```

        For example:

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        ctx.declare(
            x=(0, 7),
            y='bool')
        u = ctx.add_expr(
            r' (x = 2) \/ y ')
        defs = dict(x=1, y=True)
        v = ctx.let(defs, u)
        assert v == ctx.true
        ```

        The argument `defs` is a `dict` with keys that are
        variable names (each name is a `str`), and values
        as follows, either:

        - all `dict` values are variable names
          (each name a `str`), or

        - all `dict` values are Python values,
          each value either a `bool` or an `int`.

        The values need to align with the set of
        values that are represented for each variable,
        which depend on what was given to
        `Context.declare()`.

        So:

        - when substituting variables for variables,
          substitute:
          - Boolean-valued variables for
            Boolean-valued variables
          - integer-valued variables for
            integer-valued variables

        - when substituting Python values for variables,
          substitute:
          - Python `int` values for
            integer-valued variables
          - Python `bool` values for
            Boolean-valued variables

        To substitute BDDs for variable names,
        use `Context.replace_with_bdd()`.

        Partial substitutions are possible too:

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        ctx.declare(
            x=(-15, 20),
            y=(0, 10))
        u = ctx.add_expr(
            r'(x < 5) /\ (y >= 2)')
        defs = dict(x=1)
        v = ctx.let(defs, u)
        assert v == ctx.add_expr('y >= 2')
        ```

        @param defs:
            `dict` that maps variable names to
            BDDs or values
        @type defs:
            one of:
            - `dict[str, str]`
            - `dict[str, bool | int]`
        @param u:
            reference to BDD root
        @type u:
            `dd.autoref.Function` or
            `dd.cudd.Function`,
            must be the root of a BDD in `self.bdd`
        @return:
            result of substitution
        @rtype:
            same as the type of `u`
        """
        return self.replace(u, defs)

    def replace(self, u, vars_to_new):
        """Substitute variables by values or variables.

        This method is considered internal.
        The interface is `Context.let()`.

        @param u:
            reference to BDD root
        @type u:
            `dd.autoref.Function` or
            `dd.cudd.Function`,
            must be the root of a BDD in `self.bdd`
        @param vars_to_new:
            `dict` that maps
            each variable name to:
            - a variable name (as `str`), or
            - a value (as `bool` or `int`).
        @return:
            result of substitution
        @rtype:
            same as the type of `u`
        """
        # `vars_to_new` must be mapping, not `None`
        if len(vars_to_new) == 0:
            return u
        assert vars_to_new, vars_to_new
        for k in vars_to_new:
            rename = stx.isinstance_str(vars_to_new[k])
            break
        if rename:
            d = _refine_renaming(vars_to_new, self.vars)
        else:
            d = _refine_assignment(vars_to_new, self.vars)
        return self.bdd.let(d, u)

    def replace_with_bdd(self, u, var_subs):
        r"""Substitute Boolean-valued variables with BDDs.

        This method performs substitution in the
        way that `LET` expressions work:

        ```tla
        LET
            a == (x = 5) /\ (y = 2)
            b == ~ a
        IN
            (a = TRUE) /\ ~ b
        ```

        The argument `var_subs` is a `dict` with
        keys that are variable names
        (each name is a `str`),
        and values that are BDDs (specifically
        each value is a reference to
        the root of a BDD in `self.bdd`).

        For example, the above expression as:

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        ctx.declare(
            a='bool',
            b='bool',
            x=(0, 15),
            y=(0, 7))
        u = ctx.add_expr(
            r' (a = TRUE) /\ ~ b ')
        a_rep = ctx.add_expr(
            r' (x = 5) /\ (y = 2) ')
        b_rep = ctx.add_expr(
            r' ~ a ')
        var_subs = dict(a=a_rep, b=b_rep)
        v = ctx.replace_with_bdd(u, var_subs)
        assert v == ctx.add_expr(
            r' (x = 5) /\ (y = 2) /\ a ')
        ```

        To substitute variable names for variable names,
        or Python values for variable names,
        use `Context.let()`.

        @param u:
            reference to BDD root
        @type u:
            `dd.autoref.Function` or
            `dd.cudd.Function`,
            must be the root of a BDD in `self.bdd`
        @return:
            result of substitution
        @rtype:
            same as the type of `u`
        """
        # this method is for now distinct from
        # `Context.replace()` due to the restriction
        # of the variables that are keys of `var_subs`
        # to be declared as Boolean-valued
        return self.bdd.let(var_subs, u)

    def forall(self, qvars, u):
        r"""Universally quantify `qvars` in `u`.

        This function applies universal quantification to
        the expression represented by the BDD `u`.
        For example, the expression:

        ```tla
        \A x \in {1, 2}:  (x = 1) => (x > 0)
        ```

        can be computed with:

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        ctx.declare(x=(0, 3))
        predicate = ctx.add_expr(
            r'(x \in 1..2)  =>  ((x = 1) => (x > 0))')
        qvars = {'x'}
        u = ctx.forall(qvars, predicate)
        assert u == ctx.true
        ```

        Calling the method `Context.forall()`
        does not call the parser. The same result can
        be computed with:

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        ctx.declare(x=(0, 3))
        u = ctx.add_expr(r'''
            \A x:
                (x \in 1..2)  =>  ((x = 1) => (x > 0))
            ''')
        assert u == ctx.true
        ```

        WARNING:

        Make sure to use large enough type hints
        when declaring variables with `Context.declare()`,
        because otherwise the results can be surprising.

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        ctx.declare(x=(-1, 1))
        print(ctx.vars)
        u = ctx.add_expr(
            r'\A x:  (x = -2) => (x = 0)')
        assert u == ctx.false
        u = ctx.add_expr(
            r'\A x:  (x = -3) => (x = 0)')
        assert u == ctx.true  # because `-3` is too small
            # for what values are represented for `'x'`
        ```

        For existential quantification,
        use `Context.exist()`.

        @param qvars:
            set of variable names
        @type qvars:
            `set[str]`
        @param u:
            reference to BDD root
        @type u:
            `dd.autoref.Function` or
            `dd.cudd.Function`,
            must be the root of a BDD in `self.bdd`
        @rtype:
            same as the type of `u`
        """
        r = self.apply('not', u)
        r = self.exist(qvars, r)
        r = self.apply('not', r)
        return r

    def exist(self, qvars, u):
        r"""Existentially quantify `qvars` in `u`.

        For example, the expression:

        ```tla
        \E x \in {1, 2}:  x = 1
        ```

        can be computed with:

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        ctx.declare(x=(0, 3))
        predicate = ctx.add_expr(
            r'(x \in 1..2) /\ (x = 1)')
        qvars = {'x'}
        u = ctx.exist(qvars, predicate)
        assert u == ctx.true
        ```

        Read the docstring of `Context.forall()`.
        """
        if len(qvars) == 0:
            return u
        qbits = bv.bit_table(qvars, self.vars)
        return self.bdd.exist(qbits, u)

    def count(self, u, care_vars=None):
        r"""Return number of satisfying assignments.

        For example:

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        ctx.declare(
            x='bool',
            y=(0, 3),
            z=(0, 7))

        n = ctx.count(ctx.false)
        assert n == 0

        n = ctx.count(ctx.true)
        assert n == 1
        n = ctx.count(ctx.true, care_vars=['x'])
        assert n == 2
        n = ctx.count(ctx.true, care_vars=['y'])
        assert n == 4
        n = ctx.count(ctx.true, care_vars=['x', 'y'])
        assert n == 8

        u = ctx.add_expr(r' x /\ y >= 1 ')
        n = ctx.count(u)
        assert n == 3
        n = ctx.count(u, care_vars=['x', 'y', 'z'])
        assert n == 3 * 8
        ```

        Use the methods `Context.pick()` and
        `Context.pick_iter()` for constructing
        satisfying assignments (each assignment
        is a `dict`).

        @param u:
            reference to root of BDD
        @type u:
            `dd.autoref.Function` or
            `dd.cudd.Function`,
            must be the root of a BDD in `self.bdd`
        @param care_vars:
            variables that
            the assignments should contain.
            Should be `support(u) <= care_vars`
            If `care_vars is None`,
            then uses `support(u)`.
        @type care_vars:
            `set` of `str`
        @return:
            integer >= 0
        @rtype:
            `int`
        """
        # We could allow `support(u) > care_vars`.
        # But that needs a dedicated BDD traversal
        # (to avoid enumeration).
        # Deferred until needed.
        support = self.support(u)
        if care_vars is None:
            care_vars = support
        assert set(care_vars) >= support, (
            care_vars, support)
        bits = _refine_vars(care_vars, self.vars)
        n = len(bits)
        c = self.bdd.count(u, n)
        assert c == int(c), c
        assert c >= 0, c
        return int(c)

    def pick(self, u, care_vars=None):
        r"""Return a satisfying assignment, or `None`.

        Examples:

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        assert ctx.pick(ctx.false) is None
        assert ctx.pick(ctx.true) == dict()
        ```

        and:

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        ctx.declare(
            x='bool',
            y=(-5, 10))
        assert ctx.pick(ctx.false) is None
        assert ctx.pick(ctx.true) == dict()

        d = ctx.pick(ctx.false, care_vars=['x'])
        assert d is None

        d = ctx.pick(ctx.true, care_vars=['x'])
        assert len(d) == 1
        assert d['x'] in {False, True}

        d = ctx.pick(ctx.true, care_vars=['x', 'y'])
        assert len(d) == 2
        assert d['x'] in {False, True}
        # y \in -16 .. 15
        assert d['y'] in set(range(-16, 16))
        ```

        Use the method `Context.pick_iter()` for
        iterating over all satisfying assignments.

        Use the method `Context.count()` to find
        the number of all satisfying assignments.

        @param u:
            reference to root of BDD
        @type u:
            `dd.autoref.Function` or
            `dd.cudd.Function`,
            must be the root of a BDD in `self.bdd`
        @param care_vars:
            variables that the
            assignments should contain;
            the assignment can contain more variables
            than these, depending on the support of `u`
        @type care_vars:
            `set[str]`
        @return:
            assignment of values to variables,
            i.e., `dict` that maps each variable name to
            a Python value
        @rtype:
            `dict | None`,
            if `dict` then:
            - `str` keys
            - each value is `int` or `bool`,
              depending on the type hint of
              the corresponding variable (key of `dict`)
        """
        return next(self.pick_iter(u, care_vars), None)

    def pick_iter(self, u, care_vars=None):
        r"""Generate first-order satisfying assignments.

        This method returns a generator.

        Examples:

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        ctx.declare(
            x=(0, 10),
            y=(3, 20),
            z='bool',
            w=(-1, 1))

        # without specifying `care_vars`
        u = ctx.add_expr(
            r' x = 2  /\  y \in 4..5  /\  ~ z ')
        gen = ctx.pick_iter(u)
        assignments = list(gen)
        assert len(assignments) == 2
        assert dict(x=2, y=4, z=False) in assignments
        assert dict(x=2, y=5, z=False) in assignments

        # with `care_vars`
        care_vars = ['x', 'y', 'z', 'w']
        gen = ctx.pick_iter(u, care_vars)
        assignments = list(gen)
        assert len(assignments) == 8
        for y in [4, 5]:
            for w in [-2, -1, 0, 1]:
                d = dict(
                    x=2, y=y, z=False, w=w)
                assert d in assignments
        ```

        Read the docstring of `Context.pick()`.

        @return:
            iterator over satisfying assignments
        @rtype:
            `collections.abc.Generator[dict]`,
            an empty generator if `u == self.false`
        """
        if care_vars is None:
            care_bits = None
        elif care_vars:
            care_bits = bv.bit_table(
                care_vars, self.vars)
        else:
            care_bits = set()
        vrs = self.support(u)
        if care_vars:
            vrs.update(care_vars)
        for bit_assignment in self.bdd.pick_iter(
                u, care_vars=care_bits):
            for d in enum._bitfields_to_int_iter(
                    bit_assignment, self.vars):
                assert set(d).issubset(vrs), (
                    d, vrs, bit_assignment)
                yield d

    def define(self, definitions):
        r"""Register operator definitions.

        The string `definitions` must
        contain definitions. Example:

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        ctx.declare(
            x=(0, 10),
            y=(0, 10),
            z=(0, 10))
        definitions = r'''
            a == x + y > 3
            b == z - x <= 0
            c == a /\ b
            '''
        ctx.define(definitions)
        #
        # definitions can then be used in
        # expressions, as follows:
        u = ctx.add_expr(
            ' ~ c ',
            with_ops=True)
        assert u == ctx.add_expr(
            r' (x + y <= 3) \/ (z > x) ')
        ```


        @param definitions:
            TLA+ definitions
        @type definitions:
            `str`
        """
        assert stx.isinstance_str(
            definitions), definitions
        bv_defs = bv._parser.parse(definitions)
        defs = _parser.parse(definitions)
        for opdef, bv_opdef in zip(defs, bv_defs):
            assert opdef.operator == '==', opdef
            name_ast, expr_ast = opdef.operands
            _, bv_ast = bv_opdef.operands
            name = name_ast.value
            if name in self.vars:
                raise ValueError(
                    'Attempted to define '
                    f'operator "{name}", '
                    f'but "{name}" already '
                    'declared as variable: '
                    f'{self.vars[name]}')
            if name in self.op:
                raise ValueError(
                    'Attempted to redefine the '
                    f'operator "{name}". '
                    f'Previous definition '
                    f'as: "{self.op[name]}"')
            s = bv_ast.flatten(
                t=self.vars, defs=self.op_bdd)
            # sensitive point:
            #     operator expressions are stored
            #         before substitutions
            #     operator BDDs are stored after
            #         operator substitutions
            # operator definitions cannot change,
            # so this should
            # not cause problems as currently arranged.
            self.op[name] = expr_ast.flatten()
            if stx.isinstance_str(s):
                self.op_bdd[name] = sym_bdd.add_expr(
                    s, self.bdd)
            else:
                # operator with non-BDD value
                self.op_bdd[name] = s

    def to_bdd(self, expr):
        """Return BDD for the formula `expr`.

        This method is synonymous to the
        method `Context.add_expr()`.

        Read the docstring of `Context.add_expr()`.

        @param expr:
            expression that is Boolean-valued
        @type expr:
            `str`
        @return:
            reference to root of BDD
        @rtype:
            `dd.autoref.Function` or
            `dd.cudd.Function`,
            is the root of a BDD in `self.bdd`
        """
        return self.add_expr(expr)

    def bdds_from(self, *expressions):
        """Return `list` of BDDs for the `expressions`.

        This method calls the method `Context.to_bdd()`
        for each item of the argument `expressions`.

        Example:

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        ctx.declare(x=(0, 10))
        u, v = ctx.bdds_from('x < 5', 'x > 7')

        # check the results
        assert u == ctx.add_expr('x < 5')
        assert v == ctx.add_expr('x > 7')
        ```

        @param expressions:
            `list` of formulas
        @type expressions:
            `list` of `str`
        @return:
            `list` of references to BDD roots
        @rtype:
            either:
            - `list` of `dd.autoref.Function`, or
            - `list` of `dd.cudd.Function`,
            depending on the type of `self.bdd`
        """
        return [self.to_bdd(e) for e in expressions]

    def add_expr(self, expr, with_ops=False):
        r"""Add first-order predicate.

        A predicate is a Boolean-valued formula.

        Examples:

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        ctx.declare(x=(0, 3), y='bool')
        # `u` points to the root of a BDD
        u = ctx.add_expr(r' (x = 1) /\ ~ y ')
        print(type(u))
        # `v` points to the root of another BDD
        v = ctx.add_expr(r' (x # 2) /\ y ')
        # `w` is the disjunction of u and v
        expr = rf'{u} \/ {v}'
        w = ctx.add_expr(expr)
        assert w == (u | v)
        print(expr)
        ```

        Use `Context.to_expr()` to convert
        BDD references to expressions.

        @param expr:
            Boolean-valued expression
        @type expr:
            `str`
        @return:
            reference to root of BDD that
            represents expression `expr`
        @rtype:
            `dd.autoref.Function` or
            `dd.cudd.Function`,
            is the root of a BDD in `self.bdd`
        """
        assert stx.isinstance_str(expr), expr
        # optional because current implementation is slow
        if with_ops:
            defs = self.op
        else:
            defs = None
        s = bv.bitblast(expr, vrs=self.vars, defs=defs)
        # was `expr` a predicate ?
        assert stx.isinstance_str(s), s
        return sym_bdd.add_expr(s, self.bdd)

    def to_expr(self, u, care=None, **kw):
        r"""Return minimal DNF of integer inequalities.

        DNF abbreviates the phrase
        "Disjunctive Normal Form".

        For now, this method requires that
        all variables in `support(u)` be integer-valued.

        Example:

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        ctx.declare(
            x=(0, 7),
            y=(0, 15))
        u = ctx.add_expr(r'(x = 4) /\ (y < 3)')
        expr = ctx.to_expr(u)
        print(expr)
        ```

        Use `Context.add_expr()` to
        create BDDs from expressions.

        @param u:
            reference to root of BDD
        @type u:
            `dd.autoref.Function` or
            `dd.cudd.Function`,
            must be the root of a BDD in `self.bdd`
        @param care:
            BDD of care set,
            specifically reference to
            root of BDD of care set
        @type care:
            same as the type of `u`
        @param kw:
            keyword args are passed to
            function `cover.dumps_cover`.
        @return:
            expression
        @rtype:
            `str`
        """
        if care is None:
            care = self.bdd.true
        cover = cov.minimize(u, care, self)
        s = cov.dumps_cover(
            cover, u, care, self, **kw)
        return s

    def assign_from(self, assignment):
        r"""Return bdd from `assignment` to variables.

        Example:

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        ctx.declare(
            x=(0, 10),
            y=(0, 12))
        assignment = dict(x=1, y=2)
        u = ctx.assign_from(assignment)
        v = ctx.add_expr(
            r'(x = 1) /\ (y = 2)')
        assert u == v
        ```

        @param assignment:
            `dict` that maps
            each variable to a value (`int` or `bool`)
            in accord with `self.vars`.
        @return:
            reference to root of BDD that
            represents the given `assignment`
        @rtype:
            `dd.autoref.Function` or
            `dd.cudd.Function`,
            is the root of a BDD in `self.bdd`
        """
        bit_values = _refine_assignment(
            assignment, self.vars)
        return self.bdd.cube(bit_values)

    def apply(self, op, u, v=None, w=None):
        r"""Apply operator `op` on operands `u, v, w`.

        Example:

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        ctx.declare(
            x='bool',
            y='bool')
        u = ctx.add_expr(r' x /\ y ')
        v = ctx.add_expr(r' ~ x /\ ~ y ')
        w = ctx.apply('or', u, v)
        assert w == ctx.add_expr('x = y')
        ```

        @param op:
            name of operator,
            read the docstring of
            `self.bdd.apply()`
        @type op:
            `str`
        @param u:
            reference to BDD root
        @param v:
            reference to BDD root
        @param w:
            reference to BDD root
        @type u:
            `dd.autoref.Function` or
            `dd.cudd.Function`
        @type v:
            same as the type of `u`
        @type w:
            same as the type of `u`
        @return:
            result of applying the operation
            specified by `op`
        @rtype:
            same as the type of `u`
        """
        return self.bdd.apply(op, u, v, w)

    def copy(self, u, other):
        r"""Copy BDD `u` from `self.bdd` to `other.bdd`.

        Example:

        ```python
        import omega.symbolic.fol as _fol

        # instantiate two context objects
        source_ctx = _fol.Context()
        other_ctx = _fol.Context()
        #
        # declare variables
        vrs = dict(
            x='bool',
            y=(0, 5))
        source_ctx.declare(**vrs)
        other_ctx.declare(**vrs)
        #
        # create a BDD in `source_ctx`
        u = source_ctx.add_expr(
            r' x /\ y = 1 ')
        #
        # copy the BDD from the
        # context `source_ctx`
        # to the context `other_ctx`
        u_copied = source_ctx.copy(u, other_ctx)
        #
        # check correctness
        u_copied_ = other_ctx.add_expr(
            r' x /\ y = 1 ')
        assert u_copied == u_copied_
        #
        # `copy` is involutive
        u_ = other_ctx.copy(u_copied, source_ctx)
        assert u == u_
        ```

        @param u:
            reference to BDD root
        @type u:
            `dd.autoref.Function` or
            `dd.cudd.Function`,
            must be the root of a BDD in `self.bdd`
        @type other:
            `Context`
        @return:
            reference to BDD root
        @rtype:
            `dd.autoref.Function` or
            `dd.cudd.Function`,
            is the root of a BDD in `other.bdd`
        """
        return self.bdd.copy(u, other.bdd)

    @property
    def false(self):
        """Return `self.bdd.false`.

        Use the property `Context.true`
        for the constant `TRUE`.

        Example:

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        assert ctx.false == ~ ctx.true
        ```
        """
        return self.bdd.false

    @property
    def true(self):
        """Return `self.bdd.true`.

        Use the property `Context.false`
        for the constant `FALSE`.

        Example:

        ```python
        import omega.symbolic.fol as _fol

        ctx = _fol.Context()
        assert ctx.true == ~ ctx.false
        ```
        """
        return self.bdd.true


def reorder(dvars, fol):
    """Shift integers up in variable order of `fol.bdd`."""
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
        # print(f'Shifting bits {bitnames} to '
        #       f'level {level}')
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
    # We could log whether `value` is within the type hints,
    # but there are valid use cases outside the type hints.
    var_bits = bv.var_to_twos_complement(var, table)
    int_bits = bv.int_to_twos_complement(value)
    p, q = bv.equalize_width(var_bits, int_bits)
    values = dict()
    for u, v in zip(p, q):
        if u.isdigit():
            assert u == v, (u, v)
        else:
            values[u] = bool(int(v))
    return values


def _assignment_to_bdd(dvars, fol):
    """Return BDD from assignment to `dvars`.

    Handles only assignments of integer values.
    """
    raise DeprecationWarning(
        'use `_refine_assignment` instead')
    conj = stx.conj(
        f'{var} = {value}'
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
        super().__init__(*arg, **kw)

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
        f'({a} <= {var}) & '
        f'({var} <= {b})')


def add_one_hot(var, a, b):
    """Return symbol table for one-hot encoding."""
    t = dict()
    for i in range(a, b):
        var = f'{var}{i}'
        d = dict(type='bool', owner='parameters', level=0)
        t[var] = d
    return t


def array_to_logic(a, counter, aut):
    """Return logic formula for Boolean array `a`.

    No array bounds produced.
    Instead, if `(counter < 0) or (counter >= len(a) - 1)`,
    then select `a[-1]`.
    Therefore, array bounds *must* be added separately.

    @param a:
        `list` of elements
    @param counter:
        name of index variable
    """
    bdd = aut.bdd
    r = a[-1]
    for i, x in enumerate(a[:-1]):
        s = f'{counter} = {i}'
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
