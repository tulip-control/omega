"""Utilities for manipulating primes (x') and support."""
# Copyright 2015-2017 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
from omega.logic import syntax as stx
from omega.symbolic import bdd as sym_bdd


def is_state_predicate(u):
    """Return `True` if `u` depends only on unprimed values."""
    return not any(stx.isprimed(var) for var in u.support)


def is_proper_action(u):
    """Return `True` if `u` depends on both primed and unprimed."""
    r = u.support
    return (
        any(stx.isprimed(var) for var in r) and
        any(not stx.isprimed(var) for var in r))


def is_primed_state_predicate(u, fol):
    """Return `True` if `u` does not depend on unprimed variables.

    Only constant parameters (rigid variables) can appear
    unprimed in `u`. Any flexible variables in `u` should
    be primed.

    An identifier that is declared only unprimed is assumed
    to be a rigid variable. If a primed sibling is declared,
    then the identifier is assumed to be a flexible variable.
    """
    unprimed_vars = (is_variable(k, fol) for k in unprimed_support(u, fol))
    return not any(unprimed_vars)


def is_action_of_player(action, player, aut):
    """Return `True` if `action` constrains only `player`.

    The `player` is represented by the variables in
    `aut.varlist[player]`.
    """
    primed = primed_support(action, aut)
    vrs = aut.vars_of_players([player])
    vrs_p = stx.prime_vars(vrs)
    r = primed.issubset(vrs_p)
    return r


def rigid_support(u, fol):
    """Return constants that `u` depends on."""
    unprimed = unprimed_support(u, fol)
    return {k for k in unprimed if is_constant(k, fol)}


def flexible_support(u, fol):
    """Return unprimed variables that `u` depends on."""
    unprimed = unprimed_support(u, fol)
    return {k for k in unprimed if is_variable(k, fol)}


def vars_in_support(u, fol):
    """Return variables that `u` depends on.

    Returns unprimed identifiers for all variables
    that occur (primed or not) in the support of `u`.
    """
    vrs = set()
    for k in fol.support(u):
        if stx.isprimed(k):
            vrs.add(stx.unprime(k))
        elif is_variable(k, fol):
            vrs.add(k)
    assert vrs == (flexible_support(u, fol) |
        {stx.unprime(s) for s in primed_support(u, fol)})
    return vrs


def print_support(u, fol):
    """Print separately unprimed and primed vars in support."""
    unprimed, primed = split_support(u, fol)
    print('Unprimed identifiers in support:')
    print(unprimed)
    print('Primed identifiers in support:')
    print(primed)


def split_support(u, fol):
    """Return unprimed, primed identifiers `u` depends on.

    This function exists as an optimization over calling
    separately `unprimed_support` and `primed_support`.
    This function calls `fol.support` once, as opposed to
    twice when performing two separate calls.

    If optimization is irrelevant, then call those other
    functions, because readability counts [PEP 20].
    """
    support = fol.support(u)
    primed = {k for k in support if stx.isprimed(k)}
    unprimed = support - primed
    return unprimed, primed


def unprimed_support(u, fol):
    """Return unprimed identifiers that `u` depends on."""
    return {k for k in fol.support(u) if not stx.isprimed(k)}


def primed_support(u, fol):
    """Return primed identifiers that `u` depends on.

    These identifiers include both variables and constants.
    """
    return {k for k in fol.support(u) if stx.isprimed(k)}


def prime(u, fol):
    """Prime state predicate `u`."""
    support = fol.support(u)
    # all identifiers are unprimed ?
    assert not any(stx.isprimed(name) for name in support), support
    # avoid priming constants
    # (no primed identifiers are declared for constants)
    vrs = {name for name in support if is_variable(name, fol)}
    let = {var: stx.prime(var) for var in vrs}
    return fol.let(let, u)


def unprime(u, fol):
    """Unprime primed variables in support of `u`."""
    primed_vars = primed_support(u, fol)
    let = {s: stx.unprime(s) for s in primed_vars}
    return fol.let(let, u)


def is_constant(name, fol):
    """Return `True` if `name` is declared as constant."""
    return not is_variable(name, fol)


def is_variable(name, fol):
    """Return `True` if `name` is declared as variable.

    The identifier `name` should be unprimed.
    """
    return stx.prime(name) in fol.vars


def joint_support(nodes, fol):
    """Return union of supports ."""
    gen = (fol.support(u) for u in nodes)
    return set().union(*gen)


def support_issubset(u, vrs, fol):
    """Return `support(u) <= vrs`.

    Use this function to ensure that only the expected
    variables occur in the expression that a BDD represents.
    This check catches several errors early.

    If `fol` is a `dd.cudd.BDD`, then variable names
    will be bits instead of first-order.

    @param vrs: `set` of variable names as `str`
    """
    support = fol.support(u)
    return support.issubset(vrs)


def pairwise_disjoint(c):
    """Return whether elements in `c` are pairwise disjoint."""
    union = set().union(*c)
    n = sum(len(u) for u in c)
    return n == len(union)


def pick(c):
    """Return an element from container `c`.

    If `c` is empty, return `None`.
    """
    return next(iter(c), None)


def rename_variables(let, u, aut):
    """Rename primed and unprimed occurrences of variables.

    @param let: `dict` that renames unprimed variable identifiers
    """
    let_primed = {stx.prime(k): stx.prime(v) for k, v in let.items()}
    let.update(let_primed)
    r = aut.let(let, u)
    support = aut.support(r)
    assert not support.intersection(let), support
    return r
