"""Dynamical system representation in first-order logic.

References
==========

Leslie Lamport
    "The temporal logic of actions"
    ACM Transactions on Programming
    Languages and Systems (TOPLAS),
    Vol.16, No.3, pp.872--923, 1994

Amir Pnueli
    "The temporal semantics of concurrent programs"
    Theoretical Computer Science (TCS)
    Vol.13, No.1, pp.45--60, 1981
"""
# Copyright 2015-2017 by California Institute of Technology
# All rights reserved. Licensed under 3-clause BSD.
#
import copy
import logging
import pprint
import weakref

from omega.logic import bitvector as bv
from omega.logic import syntax as stx
from omega.symbolic import fol as _fol
from omega.symbolic import prime as prm
from omega.symbolic import symbolic as _sym
from omega.symbolic import _type_hints as tyh


log = logging.getLogger(__name__)


class Automaton(_fol.Context):
    """A changing system.

    Both interleaving and noninterleaving style specifications
    can be written using this class.
    This class can be used to represent temporal operators.
    For example, a closed system, or an open system
    described by stepwise implication.


    User-defined attributes
    =======================

    You define the attributes:

      - `vars`: `dict` that maps each variable name to
        a `dict` with keys:

          - `"type": "boolean" or "modwrap" or "saturating"`
          - `"dom": (min, max)`, range of integer
          - `"init"`: has suitable `__str__` (and is optional)

      - `varlist`: `dict(list)` that maps strings to lists of
        variable names (as strings).
        Usually used to store variables that represent each component.

      - `init`: initial condition
        `ExprDict` that maps strings to BDD nodes.
        Usually the strings are operator names.

      - `action`: transition predicate
        `ExprDict` that maps strings to BDD nodes.
        Usually the strings are operator names.

      - `win`: winning condition. In general, it takes the form:

        ```
        {
            component_name:
                {'<>[]': `list` of BDD nodes,
                 '[]<>': `list` of BDD nodes}
            another_component_name:
                {'<>[]': `list` of BDD nodes,
                 '[]<>': `list` of BDD nodes},
                ...,
            '[]<>': `list` of BDD nodes,
            '<>[]': `list` of BDD nodes
        }
        ```

        Not all these keys need to be present at once.
        Different use cases require different keys.
        For example, a synthesizer accesses the keys
        `'[]<>'` and `'<>[]'`.

      - `bdd`: change this only if you want a different BDD manager.

    The attributes `init` and `action` convert expressions to BDDs,
    for example:

    ```python
    aut.init['env'] = 'x = 0'
    >>> aut.init
    {'env': Function (DdNode) with var index: 3,
            ref count: 2, int repr: 41529443}
    ```

    The attribute `win` is a `dict` and you have to do the conversions.
    Use the method `bdds_from` to simplify code, for example:

    ```python
    aut.win['[]<>'] = aut.bdds_from('x = 0', 'y > 1')
    ```
    """
    # Relation to `omega.symbolic.symbolic.Automaton`
    # ===============================================
    #
    # - uvars = varlists["env"]
    # - upvars = varlists["env'"]
    # - evars = varlists["sys"]
    # - epvars = varlists["sys'"]
    #
    # Memoizing the following is unnecessary:
    #
    #   ubvars, ebvars, uevars, uepvars
    #
    # They are rarely used. Their relevance is to priming and
    # unpriming, which is better done by suitable functions
    # on identifiers.

    # Metalinguistic purposes served by attributes
    # stored in an `Automaton`:
    #
    # - substitution (renaming maps)
    # - grouping variables to feed quantifiers later
    # - defining operators.

    # Note: The keys of the attributes `init`, `action`
    # and `win` can be regarded also as operators.
    # In other words, `init['env']` serves as `EnvInit`,
    # and `action['env']` as `EnvNext`.

    def __init__(self):
        super(Automaton, self).__init__()
        # `varlist` says which variables represent each component
        # essentially, `varlist` is Lamport's `\mu`
        self.varlist = dict()
            # groups of variables for various uses
        self.players = dict()  # player (str) -> turn (int)
        # state machine attributes
        self.init = ExprDict(self)
        self.action = ExprDict(self)
        self.win = dict()
        # BDD cache
        self._bdd_to_expr = dict()  # BDD node -> `str`

    def __copy__(self):
        other = type(self)()
        other.vars = copy.deepcopy(self.vars)
        other.bdd = self.bdd
        other.varlist = copy.deepcopy(self.varlist)
        other.players = copy.deepcopy(self.players)
        other.op = copy.deepcopy(self.op)
        other.op_bdd = copy.copy(self.op_bdd)
        # BDD nodes
        other.init = ExprDict(other, self.init)
        other.action = ExprDict(other, self.action)
        other.win = _copier(self.win)
        return other

    def __str__(self):
        c = list()
        s = 'Variables: \n {v}'.format(
            v=pprint.pformat(self.vars))
        c.append(s)
        for k, v in self.init.items():
            e = self._fetch_expr(v)
            if e is None:
                e = v
            s = 'init[{k}] = {e}'.format(k=k, e=e)
            c.append(s)
        for k, v in self.action.items():
            e = self._fetch_expr(v)
            if e is None:
                e = v
            s = 'action[{k}] = {e}'.format(k=k, e=e)
            c.append(s)
        c.append('win =')
        c.append(str(self.win))
        return 'Automaton:\n' + '\n'.join(c)

    def declare_variables(self, **vrs):
        """Declare unprimed and primed identifiers.

        These identifiers represent the values of
        (flexible) variables.
        """
        d = bv.make_symbol_table(vrs)
        self.add_vars(d, flexible=True)

    def declare_constants(self, **constants):
        """Declare unprimed identifiers.

        These identifiers represent constants,
        also known as rigid variables.
        """
        d = bv.make_symbol_table(constants)
        self.add_vars(d, flexible=False)

    def add_vars(self, vrs, flexible=False):
        """Declare variables `vrs`.

        Refine integer-valued variables by
        Boolean-valued variables, and create maps for
        concrete variables (bits).

        @param flexible: if `True`, then add also variables
            with primed names. Assumes that `vrs` contains
            unprimed names.
        """
        assert vrs, vrs
        assert isinstance(flexible, bool), flexible  # catch kw conflict
        if flexible:
            vrs = _sym.add_primed_too(vrs)
        super(Automaton, self).add_vars(vrs)

    @property
    def vars_of_all_players(self):
        """Set of variables of all players."""
        return self.vars_of_players(self.players)

    def vars_of_players(self, players):
        """Set of variables controlled by `players`."""
        gen = (
            v for k, v in self.varlist.items()
            if k in players)
        return set().union(*gen)

    def prime_varlists(self, keys=None):
        """Map primed `keys` to lists of primed variables.

        For each `k in keys`, add `"{k}'".format(k=k)` to
        `self.varlist`, with value the `list` that results
        from priming the variables in `self.varlist[k]`.

        If `keys is None`, prime all unprimed variable lists.
        """
        if keys is None:
            keys = set(self.varlist)
        for k in keys:
            if stx.isprimed(k):
                continue
            pk = stx.prime(k)
            pvrs = stx.prime_vars(self.varlist[k])
            self.varlist[pk] = pvrs

    def replace_with_primed(self, vrs, u):
        r"""Substitute primed for unprimed `vrs` in `u`.

        For example:

        ```
        u = aut.add_expr("x /\ y /\ z")
        vrs = ['x', 'y']
        v = aut.replace_with_primed(vrs, u)
        v_ = aut.add_expr("x' /\ y' /\ z")
        assert v == v_
        ```

        Identifiers in `vrs` should be declared as variables.
        Identifiers declared as constants will raise errors.
        """
        let = {k: stx.prime(k) for k in vrs}
        return self.let(let, u)

    def replace_with_unprimed(self, vrs, u):
        """Substitute unprimed `vrs` for primed in `u`."""
        let = {stx.prime(k): k for k in vrs}
        return self.let(let, u)

    def implies_type_hints(self, u, vrs=None):
        """Return `True` if `u => TypeHints` for `vrs`.

        If `vrs is None`, then all declared variables and constants
        are taken into account.
        """
        # This function is not named `assert_type_invariant`
        # because the assertion is about the state predicate `u`,
        # so a static conclusion.
        #
        if vrs is None:
            vrs = {var for var in self.vars
                   if not stx.isprimed(var)}
        type_hints = tyh._conjoin_type_hints(vrs, self)
        r = type_hints | ~ u
        return r == self.true

    def type_hint_for(self, vrs):
        """Return conjunction of type hints for `vrs`.

        `vrs` may contain primed or unprimed identifiers.

        See also `self.type_action_for`.
        """
        return self._type_hints_to_formulas(vrs, action=False)

    def type_action_for(self, vrs):
        r"""Return action using type hints for `vrs`.

        The type action has the form:

            TypeAction == Inv /\ Inv'

        where `Inv` is a box. A box is a conjunction of integer
        intervals, one for each variable. For each integer variable,
        the interval constraint has the form:

            var \in min_value .. max_value

        The implementation supports only integer variables,
        so the interval constraint is implemented as the
        conjunction of two inequalities:

            /\ min_value <= var
            /\ var <= max_value

        If we take the closure, the second conjunct will
        result from the type invariant. The above is usable
        with either approach (with or without closure).

        We omit the type action for Boolean variables,
        because we use BDDs underneath.

        @return: formula as `str`
        """
        # to obtain a BDD, pass the result to the method `to_bdd`
        return self._type_hints_to_formulas(vrs, action=True)

    def _type_hints_to_formulas(self, vrs, action):
        r"""Return type constraint for `vrs` as `str`.

        If `action is False` then return type invariant `Inv`,
        else the action `Inv /\ Inv'`.
        """
        r = list()
        for var in vrs:
            hints = self.vars[var]
            if hints['type'] == 'bool':
                continue
            assert hints['type'] == 'int', hints
            a, b = hints['dom']
            s = r'({a} <= {var}) /\ ({var}  <= {b})'
            type_inv = s.format(a=a, b=b, var=var)
            r.append(type_inv)
            if not action:
                continue
            type_inv_primed = s.format(
                a=a, b=b, var=stx.prime(var))
            r.append(type_inv_primed)
        return stx.conj(r)

    def _cache_expr(self, expr):
        """Overwrite cache entry for BDD described by `expr`."""
        # If the `uid` for this `expr` is absent from the cache,
        # then no formula with this BDD has been added before,
        # or was, then became invalid, and has been garbage collected.
        #
        # If the `uid` is present in the cache,
        # then there are two cases:
        #
        # If the cache entry is valid, then it can only
        # have remained valid since added (or invalidated and
        # re-added by coincidence).
        #
        # However, the same `uid` can result from expressions
        # *other* than `expr`. In that case, the cache is
        # overwritten by a semantically equivalent expression.
        #
        # If the cache entry is invalid, then it should be
        # garbage collected, which leads to the case of
        # the pair `uid, expr` being absent from the cache.
        u = self._add_expr(expr)
        # We store the node ID in order to avoid incrementing the
        # reference count, to allow for garbage collection of the BDD.
        # Thus, caching here leaves the BDD manager behavior
        # unaffected. Otherwise we would produce eternal references.
        uid = self._uid_of_node(u)
        # overwritten ?
        old_expr = self._bdd_to_expr.get(uid)
        if old_expr is not None:
            log.info((
                'BDD cache entry for expression "{old}" '
                'overwritten by expression "{new}"'
                ).format(old=old_expr, new=expr))
        self._bdd_to_expr[uid] = expr
        return u

    def _fetch_expr(self, u):
        """Return cached expression for BDD node `u`.

        Return `None` if no expression remains cached for `u`.
        """
        uid = self._uid_of_node(u)
        expr = self._bdd_to_expr.get(uid)
        # The BDD `u` was never cached (user never entered it
        # via `add_expr`), or has been garbage collected and
        # then the invalid cache cleared.
        if expr is None:
            return None
        # outdated cache ?
        #
        # This can happen if all refs to `u` had been deleted,
        # then `u` was garbage collected, and the ID
        # assigned to a new node.
        #
        # It is possible (though unlikely) that `u` is
        # garbage collected, and the same ID assigned later
        # to the same Boolean formula.
        u_ = self._add_expr(expr)
        # valid cache ?
        if u == u_:
            return expr
        # It is impossible that the user has added `u`,
        # and then the cache became invalid.
        # The cache can become invalid only if the user
        # deletes all their references to `u`.
        #
        # If they do so, then it means that they aren't interested
        # in `u`, and `u` isn't referenced anywhere any more.
        #
        # Of course, `u` could then be computed via some
        # operations, but in that case it is a result,
        # not user input any more.
        #
        # Also, if the user deletes all references, and the
        # cache becomes invalid, and then the user adds the
        # same expression, then the expression will be
        # cached again, in a new valid cache entry.
        #
        # rm invalid cache entry
        self._bdd_to_expr.pop(uid)

    def _clear_invalid_cache(self):
        """Pop any BDD cache entries no longer valid."""
        invalid = set()
        for uid, expr in self._bdd_to_expr.items():
            u = self._add_expr(expr)
            uid_ = self._uid_of_node(u)
            # valid cache entry ?
            if uid == uid_:
                continue
            invalid.add(uid)
        # rm invalid cache entries
        [self._bdd_to_expr.pop(uid) for uid in invalid]

    def _uid_of_node(self, u):
        """Return unique identifier `str` of BDD node `u`."""
        return str(u)

    # lesson: don't call this, because the `uid`
    # may be invalid in the BDD manager.
    def _node_with_uid(self, uid):
        """Return BDD node identified by the string `uid`."""
        return self.bdd.add_expr(uid)

    def _add_expr(self, expr):
        """Return BDD for expression without caching it.

        Use `self.op_bdd` or `self.add_expr`.
        """
        if expr in self.op_bdd:
            return self.op_bdd[expr]
        return self.add_expr(expr)

    def build(self):
        """Prime variable lists in `self.varlist`."""
        self.prime_varlists(['env', 'sys'])


def _assert_invariant(components, aut, moore=True):
    """Assert invariant about `aut.varlists` and predicates.

    - varlists of `components` are disjoint
    - `aut.init` and `aut.win` contain state predicates

    If `moore=True`, then assert that `aut.action` are actions
    of `components`.
    """
    varlists = {k: v for k, v in aut.varlist.items()
                if k in components}
    actions = {k: v for k, v in aut.actions.items()
               if k in components}
    assert prm.pairwise_disjoint(varlists), varlists
    for u in aut.init.values():
        assert prm.is_state_predicate(u)
    _assert_is_win(aut.win)
    if not moore:
        return
    for component, action in actions.items():
        assert prm.is_action_of_player(action, component, aut)


def _assert_is_win(d):
    if isinstance(d, list):
        for u in d:
            assert prm.is_state_predicate(u), u
            return
    assert isinstance(d, dict), d
    for _, v in d.items():
        _assert_is_win(v)


class ExprDict(dict):
    """A `dict` that converts expressions to BDDs.

    Setting a string as value triggers a conversion to
    a BDD first, then storage. To reverse this conversion
    call the method `_fetch_expr` of the associated context.

    This class treats values other than `str` the same
    way that `dict` does.
    """

    def __init__(self, context, *arg, **kw):
        super(ExprDict, self).__init__(*arg, **kw)
        self._context = weakref.proxy(context)

    def __setitem__(self, k, v):
        """Set key `k` to value `v`.

        If `v` is a `str`, then convert to BDD,
        then set `k` to the resulting BDD.
        Otherwise behave as a `dict`.
        """
        try:
            v + ''
        except TypeError:
            super(ExprDict, self).__setitem__(k, v)
            return
        if v in self._context.op_bdd:
            u = self._context.op_bdd[v]
        else:
            u = self._context._cache_expr(v)
        super(ExprDict, self).__setitem__(k, u)

    def update(self, *arg, **kw):
        if arg:
            (d,) = arg
            kw.update(d)
        for k, v in kw.items():
            self[k] = v

    def setdefault(self, key, value=None):
        """Return self[key], after setting if needed.

        If `key not in self` and `value` is a `str`,
        then the returned value is a BDD.
        See `__setitem__` for more details.
        """
        if key not in self:
            self[key] = value
        return self[key]


def conj_actions_of(players, aut):
    """Return conjunction of actions from `players`."""
    action = aut.true
    for p in players:
        action &= aut.action[p]
    return action


# serves the same purpose as `fill_blanks` in `symbolic`.
def default_streett_automaton():
    """Return an `Automaton` populated as Streett spec."""
    aut = _default_safety_automaton()
    aut.win['[]<>'] = [aut.true]
    aut.win['<>[]'] = [aut.false]
    return aut


def default_rabin_automaton():
    """Return an `Automaton` populated as Rabin spec."""
    aut = _default_safety_automaton()
    aut.win['[]<>'] = [aut.true]
    aut.win['<>[]'] = [aut.true]
    return aut


def _default_safety_automaton():
    """Return a populated `Automaton`, except for liveness."""
    aut = Automaton()
    aut.varlist = dict(env=list(), sys=list())
    aut.init.update(env=aut.true, sys=aut.true)
    aut.action.update(env=aut.true, sys=aut.true)
    aut.qinit = r'\E \A'
    aut.moore = True
    aut.plus_one = True
    return aut


def _copier(d):
    """Recursively copy `d`, used for `self.win`."""
    if isinstance(d, list):
        return list(d)
    assert isinstance(d, dict), d
    r = dict()
    for k, v in d.items():
        r[k] = _copier(v)
    return r
