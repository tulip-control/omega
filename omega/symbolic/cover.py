"""Symbolic computation of minimal cover with orthotopes.

References
==========

Olivier Coudert
    "Two-level logic minimization: An overview"
    Integration, the VLSI Journal
    Vol.17, No.2, Oct 1994, pp.97--140
    http://dx.doi.org/10.1016/0167-9260(94)00007-7
"""
# Copyright 2016 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
from __future__ import absolute_import
from __future__ import print_function
from itertools import cycle
import logging
import time

import natsort
from omega.logic import syntax as stx
from omega.symbolic.bdd import support_issubset
from omega.symbolic.bdd import joint_support
# import polytope (inline)


log = logging.getLogger(__name__)


VAR_OWNER = 'other'


def minimize(f, care, fol):
    """Compute minimal DNF of predicate `f` over integers.

    @param f: predicate over integer-valued variables
    @param care: care set as predicate over same variables
    @type f, care: BDD node
    @type fol: `omega.symbolic.fol.Context`

    @return: minimal cover as BDD over parameters
    @rtype: BDD node
    """
    # reasons for permisiveness here:
    #
    # - enable inspecting env violations of assumption
    # - make errors visible
    # - use entire instantiation domain
    # - permit computing DNF for care set using same `fol.vars`
    # - tests
    if not _care_implies_type_hints(f, care, fol):
        log.warning('care set should imply type hints')
    # could let
    #     f &= care
    # but explicit is better.
    # Also, this permits working outside type hints.
    if not _f_implies_care(f, care, fol):
        log.warning('f should imply care set')
    if (f | ~ care) == fol.true:
        log.warning('f covers care set, so trivial cover')
    log.info('---- branching ----')
    path_cost = 0.0
    x_vars, px, qx, p_to_q = _setup_aux_vars(f, care, fol)
    u_leq_p, p_leq_u = _partial_order(px, fol)
    varmap = _parameter_varmap(px, qx)
    p_leq_q = _orthotope_subseteq(varmap, fol)
    p_eq_q = _orthotope_eq(varmap, fol)
    # covering problem
    fcare = f | ~ care
    # the slack is introduced by having more primes
    # (those for `fcare`) to cover the same minterms (`f`)
    x = _embed_as_implicants(f, px, fol)
    y = prime_orthotopes(
        fcare, px, qx,
        p_leq_q, p_eq_q,
        fol, x_vars)
    bab = _BranchAndBound(
        p_leq_q, p_leq_u, u_leq_p,
        p_eq_q, p_to_q, px, qx, fol)
    # initialize upper bound
    bab.upper_bound = _upper_bound(
        x, y, p_leq_q, p_to_q, fol)
    # assert covers(bab.best_cover, f, p_leq_q, p_to_q, px, fol)
    cover, _ = _branch(
        x, y,
        u_leq_p, p_leq_u, p_leq_q, p_eq_q,
        p_to_q, px, qx, path_cost, bab, fol)
    if cover is None:
        cover = _some_cover(x, y, p_leq_q, p_to_q, fol)
    assert cover is not None
    assert _covers(cover, f, p_leq_q, p_to_q, px, fol)
    low = care & ~ f
    assert _none_covered(cover, low, p_to_q, px, qx, fol)
    log.info('==== branching ==== ')
    return cover


def _branch(
        x, y,
        u_leq_p, p_leq_u, p_leq_q, p_eq_q,
        p_to_q, px, qx, path_cost, bab, fol):
    """Recursive call of `branch`."""
    log.info('\n\n---- _branch (recursive) ----')
    t0 = time.time()
    xcore, ycore, essential = _cyclic_core_fixpoint(
        x, y,
        u_leq_p, p_leq_u, p_leq_q, p_eq_q,
        p_to_q, px, qx, fol)
    _print_cyclic_core(
        x, y, xcore, ycore, essential,
        t0, px, fol)
    # C_left.path =
    #     C.path + 1  (* already from `_recurse` *)
    # C_left.lower =
    #     + Cardinality(essential_left)  (* `_cost` *)
    #     + LowerBound(core_left)  (* `lb` below *)
    #
    # C_right.path =
    #     C.path  (* already from `_recurse` *)
    # C_right.lower =
    #     + Cardinality(essential_right)
    #     + LowerBound(core_right)
    cost_ess = _cost(essential, p_to_q, fol)
    path_cost += cost_ess
    if xcore == fol.false:
        log.info('empty cyclic core: stop recursion')
        bab.upper_bound = path_cost
        lb = cost_ess
        log.info('==== _branch (recursive) ====\n')
        return essential, lb
    # prune
    lb_core = _lower_bound(xcore, ycore, p_leq_q, p_to_q, fol)
    c = path_cost + lb_core
    # lower bound only once at the top
    # because farther below in the search tree the
    # lower bounds are local, not global
    if bab.lower_bound is None:
        bab.lower_bound = c
    assert c > 0, c
    # C_left.path + C_left.lower >= global_upper_bound ?
    # C_right.path + C_right.lower >= global_upper_bound ?
    if c >= bab.upper_bound:
        log.info('prune')
        lb = cost_ess + lb_core
        log.info('==== _branch (recursive) ====\n')
        return None, lb
    assert c < bab.upper_bound, (c, bab.upper_bound)
    # branch
    assert xcore != fol.false
    assert ycore != fol.false
    # pick branching element
    e = None
    log.info('start picking')
    for d in fol.pick_iter(ycore):
        r = _recurse(
            d, xcore, ycore,
            u_leq_p, p_leq_u, p_leq_q, p_eq_q,
            p_to_q, px, qx, path_cost, bab, fol)
        if e is None:
            e = r
        if _cost(r, p_to_q, fol) < _cost(e, p_to_q, fol):
            e = r
        if bab.lower_bound == bab.upper_bound:
            log.info(
                'converged: upper = lower = {c}'.format(
                    c=bab.upper_bound))
            break
    cover = e | essential
    # `path_cost` forwards shallower info
    # would need similar cumulative essentials +
    # picked primes info in order to update `bab.best_cover`
    log.info('==== _branch (recursive) ====\n')
    return cover, None


def _recurse(
        d, x, y,
        u_leq_p, p_leq_u, p_leq_q, p_eq_q,
        p_to_q, px, qx, path_cost, bab, fol):
    log.info('\n\n---- recurse ----')
    log.info('picked branching y:')
    log.info(d)
    y_branch = fol.assign_from(d)
    in_ycore = ~ y_branch | y
    assert in_ycore == fol.true
    ynew = y & ~ y_branch
    assert ynew != y
    # branch
    # r(p) == p <= y_branch
    dq = {p_to_q[k]: v for k, v in d.items()}
    r = fol.let(dq, p_leq_q)
    x_minus_y = x & ~ r
    assert x_minus_y != x  # must prove always the case
    e0, lb_left = _branch(
        x_minus_y, ynew,
        u_leq_p, p_leq_u, p_leq_q, p_eq_q,
        p_to_q, px, qx, path_cost + 1, bab, fol)
    # pruning with left lower bound (Thm.7 [Coudert 1994])
    if path_cost + lb_left >= bab.upper_bound:
        e1, _ = _branch(
            x, ynew,
            u_leq_p, p_leq_u, p_leq_q, p_eq_q,
            p_to_q, px, qx, path_cost, bab, fol)
    else:
        e1 = None
    # pick cheaper
    cost_0 = _cost(e0, p_to_q, fol)
    cost_1 = _cost(e1, p_to_q, fol)
    if cost_0 < cost_1:
        e = e0 | y_branch
    else:
        e = e1
    log.info('==== recurse ====\n')
    return e


def _cost(u, p_to_q, fol):
    """Return numerical cost of cover `u`."""
    if u is None:
        return float('inf')
    # cost of each implicant = 1
    # cost of a cover = number of implicants it contains
    assert support_issubset(u, p_to_q, fol)
    n = fol.count(u)
    return n


def cyclic_core(f, care, fol):
    """Shallow minimal cover, only up to cyclic core."""
    log.info('cyclic core computation')
    t0 = time.time()
    # assert
    assert f in fol.bdd, f
    assert care in fol.bdd, care
    assert care != fol.false, 'empty care set'
    assert f != fol.false, 'nothing to cover'
    assert f != fol.true or care != fol.true, (
        'no variables involved in problem')
    x_vars, px, qx, p_to_q = _setup_aux_vars(f, care, fol)
    fcare = ~ care | f
    u_leq_p, p_leq_u = _partial_order(px, fol)
    varmap = _parameter_varmap(px, qx)
    p_leq_q = _orthotope_subseteq(varmap, fol)
    p_eq_q = _orthotope_eq(varmap, fol)
    # covering problem
    x = _embed_as_implicants(f, px, fol)
    y = prime_orthotopes(
        fcare, px, qx,
        p_leq_q, p_eq_q,
        fol, x_vars)
    # assert problem is feasible
    assert x != fol.false
    assert y != fol.false
    assert _covers(y, f, p_leq_q, p_to_q, px, fol)
    xcore, ycore, essential = _cyclic_core_fixpoint(
        x, y,
        u_leq_p, p_leq_u, p_leq_q, p_eq_q,
        p_to_q, px, qx, fol)
    if xcore == fol.false:
        assert _covers(essential, f, p_leq_q, p_to_q, px, fol)
    _print_cyclic_core(
        x, y, xcore, ycore, essential,
        t0, px, fol)
    s = dumps_cover(essential, f, care, fol)
    log.info(s)
    return xcore, ycore, essential


def _print_cyclic_core(
        x, y, xcore, ycore, essential,
        t0, px, fol):
    """Print results of cyclic core computation.

    Assert support and covering properties.
    """
    # assert
    params = _collect_parameters(px)
    if essential != fol.false:
        assert support_issubset(essential, params, fol)
    if xcore != fol.false:
        assert support_issubset(xcore, params, fol)
    if ycore != fol.false:
        assert support_issubset(ycore, params, fol)
    # print
    m = fol.count(x)
    n = fol.count(y)
    log.info(
        '({m}, {n}) implicants in (x, y)'.format(
            m=m, n=n))
    m = fol.count(xcore)
    n = fol.count(ycore)
    log.info(
        '({m}, {n}) implicants in cyclic core'.format(
            m=m, n=n))
    n = fol.count(essential)
    log.info('{n} primes are essential'.format(n=n))
    t1 = time.time()
    dt = t1 - t0
    log.info('cyclic core took {dt:1.2f} sec'.format(dt=dt))


def _cyclic_core_fixpoint(
        x, y,
        u_leq_p, p_leq_u, p_leq_q, p_eq_q,
        p_to_q, px, qx, fol):
    """Return cyclic core and essential elements."""
    log.debug('\n\n---- cyclic core fixpoint ----')
    # assert
    assert x in fol.bdd, x
    assert y in fol.bdd, y
    pvars = set(p_to_q)
    assert support_issubset(x, pvars, fol)
    assert support_issubset(y, pvars, fol)
    # compute
    essential = fol.false
    xold = None
    yold = None
    i = 0
    while x != xold or y != yold:
        log.debug('starting iteration {i}'.format(i=i))
        t0 = time.time()
        xold = x
        yold = y
        x = _max_transpose(
            x, y,
            u_leq_p, p_leq_u, p_leq_q, p_eq_q,
            p_to_q, px, qx, fol,
            signatures=True)
        e = x & y
        x = x & ~ e
        y = y & ~ e
        essential |= e
        y = _max_transpose(
            x, y,
            u_leq_p, p_leq_u, p_leq_q, p_eq_q,
            p_to_q, px, qx, fol)
        t1 = time.time()
        dt = t1 - t0
        log.debug('iteration {i} took {dt:1.2f} sec'.format(
            i=i, dt=dt))
        i += 1
    _assert_fixpoint(x, y, xold, yold, essential, pvars, fol)
    log.debug('==== cyclic core fixpoint ====\n')
    return x, y, essential


def _assert_fixpoint(x, y, xold, yold, essential, pvars, fol):
    """Assert `x, y = xold, yold` and check supports."""
    assert x == xold
    assert y == yold
    e = x & y
    assert e == fol.false, e
    e = x & essential
    assert e == fol.false, e
    e = y & essential
    assert e == fol.false, e
    assert support_issubset(x, pvars, fol)
    assert support_issubset(y, pvars, fol)
    assert support_issubset(essential, pvars, fol)


def _max_transpose(p_is_signature, p_is_prime,
                   u_leq_p, p_leq_u, p_leq_q, p_eq_q,
                   p_to_q, px, qx, fol, signatures=False):
    """Maximal transposed primes or signatures.

    (max tau_Y(X) or max tau_X(Y))

    @param signatures: if `True`, then transpose signatures,
        otherwise primes.

    Requires that `p, p', q` be in `fol.vars` and
    be refined by the same number of bits each.
    """
    log.info('---- max transpose ----')
    # assert
    p_vars = set(p_to_q)
    assert support_issubset(p_is_prime, p_vars, fol)
    assert support_issubset(p_is_signature, p_vars, fol)
    # compute
    u = _transpose(
        p_is_signature, p_is_prime,
        u_leq_p, p_leq_u,
        p_to_q, fol, signatures=signatures)
    r = _maxima(u, p_leq_q, p_eq_q, p_to_q, fol)
    assert support_issubset(r, p_vars, fol)
    log.info('==== max transpose ====')
    return r


def _transpose(p_is_signature, p_is_prime,
               u_leq_p, p_leq_u,
               p_to_q, fol, signatures=False):
    """Transpose primes (tau_X(Y)) or signatures (tau_Y(X)).

    @param p_is_prime: some primes, function of `p`
    @param p_is_signature: function of `p`
    @param p_to_q: mapping from `p` to `q`
    @param signatures: if `True`, then transpose signatures,
        otherwise primes.
    """
    log.info('---- tranpose ----')
    if signatures:
        p_is_signature, p_is_prime = p_is_prime, p_is_signature
        u_leq_p, p_leq_u = p_leq_u, u_leq_p
    # assert
    p_vars = set(p_to_q)
    assert support_issubset(p_is_prime, p_vars, fol)
    assert support_issubset(p_is_signature, p_vars, fol)
    # p' used as u
    p_to_u = {p: _prime_like(p) for p in p_vars}
    u_is_signature = fol.let(p_to_u, p_is_signature)
    # same coverage
    p_like_q = _contains_covered(
        u_is_signature, u_leq_p, p_to_q, p_to_u, fol)
    u_like_q = fol.let(p_to_u, p_like_q)
    # u_is_prime = fol.let(p_to_u, p_is_prime)
    q_is_prime = fol.let(p_to_q, p_is_prime)
    #
    q = p_to_q.values()
    u = p_to_u.values()
    r = ~ u_like_q | p_leq_u
    r = fol.forall(u, r)
    r &= p_like_q
    r &= q_is_prime
    r = fol.exist(q, r)
    '''
    q = ', '.join(iter(p_to_q.values()))
    u = ', '.join(iter(p_to_u.values()))
    s = (
        '\E {q}:  @{q_is_prime} /\ @{p_like_q} /\ '
        '    \A {u}:  @{u_like_q} => @{p_leq_u}').format(
            q=q,
            u=u,
            q_is_prime=q_is_prime,
            p_like_q=p_like_q,
            u_like_q=u_like_q,
            p_leq_u=p_leq_u)
    r = fol.add_expr(s)
    '''
    assert support_issubset(r, p_vars, fol)
    log.info('==== tranpose ====')
    return r


def _contains_covered(u_is_signature, u_leq_p,
                      p_to_q, p_to_u, fol):
    """Return primes that cover all signatures under prime.

    Require that `p_to_u` be given explicitly,
    to avoid errors if support is empty.

    @param signatures: function of `u`
    @param u_leq_p: partial order `u <= p`
    @param p_to_q: mapping from `p` to `q`
    @type rename: `dict`
    """
    log.info('---- contains covered ----')
    # assert
    p_vars = set(p_to_q)
    q_vars = set(p_to_q.values())
    u_vars = set(p_to_u.values())
    pq_vars = p_vars.union(q_vars)
    pu_vars = p_vars.union(u_vars)
    assert not p_vars & q_vars, (p_vars, q_vars)
    assert not p_vars & u_vars, (p_vars, u_vars)
    assert not u_vars & q_vars, (u_vars, q_vars)
    assert support_issubset(u_is_signature, u_vars, fol)
    assert support_issubset(u_leq_p, pu_vars, fol)
    # compute
    u_leq_q = fol.let(p_to_q, u_leq_p)
    r = u_is_signature & u_leq_q
    r = ~ r | u_leq_p
    r = fol.forall(u_vars, r)
    '''
    uvars = ', '.join(u_vars)
    s = (
        '\A {uvars}:  '
        '    (@{sig_u} /\ @{u_leq_q}) '
        '        => @{u_leq_p}').format(
        uvars=uvars,
        sig_u=u_is_signature,
        u_leq_q=u_leq_q,
        u_leq_p=u_leq_p)
    r = fol.add_expr(s)
    '''
    assert support_issubset(r, pq_vars, fol)
    log.info('==== contains covered ====')
    return r


def _maxima(u, p_leq_q, p_eq_q, p_to_q, fol):
    """Return maximal elements of `u` wrt `p_leq_q`.

    @param u: function of `p`
    @param p_leq_q: partial order `p <= q`
        (anti-symmetry required: a quasi-order does not work.)
    @param p_to_q: mapping from `p` to `q`
    @type p_to_q: `dict`
    """
    # assert
    p_vars = set(p_to_q)
    assert support_issubset(u, p_vars, fol)
    q_vars = set(p_to_q.values())
    pq_vars = p_vars.union(q_vars)
    assert support_issubset(p_leq_q, pq_vars, fol)
    # compute
    v = fol.let(p_to_q, u)
    #
    r = v & p_leq_q
    r = ~ r | p_eq_q
    r = fol.forall(q_vars, r)
    r &= u
    '''
    p_eq_q = stx.conj('{pj} = {qj}'.format(pj=pj, qj=qj)
                      for pj, qj in p_to_q.items())
    q = ', '.join(q_vars)
    s = (
        '@{u} /\ '
        '\A {q}:  (@{v} /\ @{p_leq_q}) => ({p_eq_q})').format(
            u=u,
            v=v,
            p_leq_q=p_leq_q,
            p_eq_q=p_eq_q,
            q=q)
    r = fol.add_expr(s)
    # '''
    assert support_issubset(r, p_vars, fol)
    return r


def _lower_bound(x, y, p_leq_q, p_to_q, fol):
    """Return lower bound (greedy)."""
    log.debug('---- lower bound ----')
    _, n = _independent_set(
        x, y, p_leq_q, p_to_q, fol, only_size=True)
    _assert_possible_cover_size(n, x, fol)
    log.info('lower bound = {n}'.format(n=n))
    log.debug('==== lower bound ====')
    return n


def _upper_bound(x, y, p_leq_q, p_to_q, fol):
    """Return upper bound (greedy)."""
    log.debug('---- upper bound ----')
    _, n = _some_cover(
        x, y, p_leq_q, p_to_q, fol, only_size=True)
    _assert_possible_cover_size(n, x, fol)
    log.info('upper bound = {n}'.format(n=n))
    log.debug('==== upper bound ====')
    return n


def _lower_bound_naive(x, y, p_leq_q, p_to_q, fol):
    """Return lower bound.

    Naive computation that greedily constructs
    an independent set.
    """
    log.debug('---- naive lower bound ----')
    z, n = _independent_set(x, y, p_leq_q, p_to_q, fol)
    assert support_issubset(z, p_to_q, fol)
    _assert_possible_cover_size(n, x, fol)
    log.info('lower bound = {n}'.format(n=n))
    log.debug('==== naive lower bound ====')
    return n


def _upper_bound_naive(x, y, p_leq_q, p_to_q, fol):
    """Return upper bound.

    Naive computation that greedily constructs
    an irredundant cover.
    """
    log.debug('---- naive upper bound ----')
    cover, n = _some_cover(x, y, p_leq_q, p_to_q, fol)
    assert support_issubset(cover, p_to_q, fol)
    _assert_possible_cover_size(n, x, fol)
    log.info('upper bound = {n}'.format(n=n))
    log.debug('==== naive upper bound ====')
    return n


def _assert_possible_cover_size(n, x, fol):
    """Raise `AssertionError` if size `u` not of a cover."""
    assert n >= 0, n
    assert (n == 0) is (x == fol.false), n


def _independent_set(
        x, y, p_leq_q, p_to_q, fol, only_size=False):
    """Return an independent set of implicants and its size.

    Requires that each implicant in `x` be covered
    by at least one implicant in `y`.

    @param only_size: Do not return the independent set.
        This avoids creating the BDD of a sparse set.
    """
    log.debug('---- independent set ----')
    p = set(p_to_q)
    q = set(p_to_q.values())
    assert support_issubset(x, p, fol), (fol.support(x), p)
    assert support_issubset(y, p, fol), (fol.support(y), p)
    yq = fol.let(p_to_q, y)
    assert _cover_refines(x, yq, p_leq_q, p, q, fol), r
    rem = x
    z = fol.false
    k = 0
    n = fol.count(rem)
    assert n >= 0, n
    while rem != fol.false:
        x0 = fol.pick(rem)
        assert set(x0) <= p, x0
        if not only_size:
            z |= fol.assign_from(x0)
        # umbrella of x0
        #
        # r(p) == \E q:  /\ x0 <= q
        #                /\ p <= q
        #                /\ y(q)
        r = yq & fol.let(x0, p_leq_q)
        r &= p_leq_q
        r = fol.exist(q, r)
        # update
        assert support_issubset(r, p, fol)
        rem &= ~ r
        k += 1
        # variant
        nold = n
        n = fol.count(rem)
        assert n < nold, (n, nold)
    assert fol.count(rem) == 0, 'some x not covered'
    _assert_possible_cover_size(k, x, fol)
    log.debug('==== independent set ====')
    if only_size:
        return None, k
    k_ = fol.count(z)
    assert k == k_, (k, k_)
    return z, k


def _some_cover(x, y, p_leq_q, p_to_q, fol, only_size=False):
    """Return a cover and its size, possibly not minimal.

    Signature similar to `_independent_set`.
    """
    log.debug('---- some cover ----')
    p = set(p_to_q)
    q = set(p_to_q.values())
    assert support_issubset(x, p, fol), (fol.support(x), p)
    assert support_issubset(y, p, fol), (fol.support(y), p)
    yq = fol.let(p_to_q, y)
    assert _cover_refines(x, yq, p_leq_q, p, q, fol), r
    rem = x
    z = fol.false
    k = 0
    n = fol.count(rem)
    assert n >= 0, n
    while rem != fol.false:
        x0 = fol.pick(rem)  # x0
        assert set(x0) <= p, x0
        # ys that cover x0
        #
        # r(q) == /\ x0 <= q
        #         /\ y(q)
        r = yq & fol.let(x0, p_leq_q)
        y0 = fol.pick(r)
        assert set(y0) <= q, y0
        if not only_size:
            z |= fol.assign_from(y0)
        # x that y0 does not cover
        # rem(p) /\ ~ (p <= y0)
        rem &= ~ fol.let(y0, p_leq_q)
        k += 1
        # variant
        nold = n
        n = fol.count(rem)
        assert n < nold, (n, nold)
    assert fol.count(rem) == 0, 'some x not covered'
    _assert_possible_cover_size(k, x, fol)
    log.debug('==== some cover ====')
    if only_size:
        return None, k
    q_to_p = {v: k for k, v in p_to_q.items()}
    zp = fol.let(q_to_p, z)
    k_ = fol.count(z)
    assert k == k_, (k, k_)
    return zp, k


def _cover_refines(xp, yq, p_leq_q, p, q, fol):
    """Return `True` if cover `xp` refines `yq`.

    In other words, if each implicant of `xp` is
    covered by some implicant in `yq` (let q == p).
    """
    # Each implicant in `x` must be covered
    # by some implicant in `y`.
    #
    # Return
    #     \A p:  \/ ~ x(p)
    #            \/ \E q:  /\ y(q)
    #                      /\ p <= q
    r = yq & p_leq_q
    r = fol.exist(q, r)
    r |= ~ xp
    r = fol.forall(p, r)
    return r == fol.true


def _partial_order(px, fol):
    """Return `u <= p` and `p <= u`."""
    ux = {
        x: dict(
            a=_prime_like(d['a']),
            b=_prime_like(d['b']))
        for x, d in px.items()}
    varmap = _parameter_varmap(ux, px)
    u_leq_p = _orthotope_subseteq(varmap, fol)
    varmap = _parameter_varmap(px, ux)
    p_leq_u = _orthotope_subseteq(varmap, fol)
    return u_leq_p, p_leq_u


def essential_orthotopes(f, px, qx, fol, xvars):
    """Return essential prime orthotopes of `f`."""
    log.info('---- essential orthotopes ----')
    varmap = _parameter_varmap(px, qx)
    p_leq_q = _orthotope_subseteq(varmap, fol)
    p_eq_q = _orthotope_eq(varmap, fol)
    p_is_prime = prime_orthotopes(
        f, px, qx,
        p_leq_q, p_eq_q,
        fol, xvars)
    # add to quantify u, v, so that we can rename
    #
    # TODO: reimplement using `fol.Context.rename`
    varmap = _parameter_varmap(qx, px)
    q_leq_p = _orthotope_subseteq(varmap, fol)
    q_is_prime = prime_orthotopes(
        f, qx, px,
        q_leq_p, p_eq_q,
        fol, xvars)
    x_in_q = _orthotope_contains_x(qx, fol)
    x = ', '.join(px)
    q = ', '.join(_collect_parameters(qx))
    s = (
        '@{p_is_prime} /\ '
        r'\E {x}:  ( '
        '    @{f} /\ '
        r'    \A {q}:  ( '
        '        ( '
        '            @{q_is_prime} /\ '
        '            ~ @{p_eq_q} '
        '        ) '
        '        => ~ @{x_in_q}'
        '    )'
        ')').format(
            p_is_prime=p_is_prime,
            q_is_prime=q_is_prime,
            p_eq_q=p_eq_q,
            x_in_q=x_in_q,
            f=f, x=x, q=q)
    r = fol.add_expr(s)
    log.info('==== essential orthotopes ====')
    return r


def prime_orthotopes(
        f, px, qx,
        p_leq_q, p_eq_q,
        fol, xvars):
    """Return dominators of implicants."""
    log.info('----- prime orthotopes ----')
    assert support_issubset(f, xvars, fol)
    p_to_q = _renaming_between_parameters(px, qx)
    p_is_implicant = _implicant_orthotopes(f, px, fol, xvars)
    q_is_implicant = fol.let(p_to_q, p_is_implicant)
    q = _collect_parameters(qx)
    r = q_is_implicant & p_leq_q
    r = p_eq_q | ~ r
    r = fol.forall(q, r)
    r = r & p_is_implicant
    '''
    q = ', '.join(_collect_parameters(qx))
    s = (
        '@{p_is_implicant} /\ '
        r'\A {q}:  ( '
        '     (@{q_is_implicant} /\ @{p_leq_q})'
        '     => @{p_eq_q}'
        ')').format(
            p_is_implicant=p_is_implicant,
            q_is_implicant=q_is_implicant,
            p_leq_q=p_leq_q,
            p_eq_q=p_eq_q,
            q=q)
    r = fol.add_expr(s)
    '''
    log.info('==== prime orthotopes ====')
    return r


def _implicant_orthotopes(f, abx, fol, xvars):
    """Return orthotopes that imply `f`.

    Caution: `fol` type hints are ignored.
    """
    log.info('---- implicant orthotopes ----')
    assert support_issubset(f, xvars, fol)
    x = ', '.join(abx)
    h = _orthotope_contains_x(abx, fol)
    nonempty = _orthotope_nonempty(abx, fol)
    s = (
        '@{nonempty} /\ '
        '\A {x}:  @{h} => @{f} ').format(
            x=x, h=h, f=f, nonempty=nonempty)
    r = fol.add_expr(s)
    log.info('==== implicant orthotopes ====')
    return r


def _none_covered(
        cover_p, f,
        p_to_q, px, qx, fol):
    """Return `True` if `cover_p` covers no minterm in `f`.

    Arguments similar to `covers`.
    """
    p = set(p_to_q)
    q = set(p_to_q.values())
    varmap = _parameter_varmap(px, qx)
    fq = _embed_as_implicants(f, qx, fol)
    # \A p:  \/ ~ cover(p)
    #        \/ ~ \E q:  /\ f(q)
    #                    /\ Intersect(p, q)
    r = fq & _orthotopes_intersect(varmap, fol)
    r = ~ fol.exist(q, r)
    r |= ~ cover_p
    r = fol.forall(p, r)
    return r == fol.true


def _covers(
        cover_p, f, p_leq_q,
        p_to_q, px, fol):
    """Return `True` if `cover_p` covers `f`.

    @param cover_p: primes, repr as `p`
    @param f: elements to cover, repr as `x`
    @param px: mapping from `p` to intervals
    """
    p = set(p_to_q)
    q = set(p_to_q.values())
    fp = _embed_as_implicants(f, px, fol)
    cover_q = fol.let(p_to_q, cover_p)
    # \A p:  \/ ~ f(p)
    #        \/ \E q:  cover(q) /\ (p <= q)
    r = cover_q & p_leq_q
    r = fol.exist(q, r)
    r |= ~ fp
    r = fol.forall(p, r)
    return r == fol.true


def _covers_naive(cover_p, f, px, fol):
    """Return `True` if `cover_p` covers `f`.

    Same as `covers`. Here the computation happens over
    the concrete variables (`x`), so it is less efficient.
    """
    x_vars = set(px)
    assert support_issubset(f, x_vars, fol)
    # concretize
    x_in_cover = _concretize_implicants(cover_p, px, fol)
    covered = ~ f | x_in_cover
    return covered == fol.true


def _concretize_implicants(implicants_p, px, fol):
    """Return covered set as function of `x`."""
    # assert
    x_vars = set(px)
    p_vars = _collect_parameters(px)
    assert support_issubset(implicants_p, p_vars, fol)
    # concretize
    x_in_p = _orthotope_contains_x(px, fol)
    u = x_in_p & implicants_p
    covered_x = fol.exist(p_vars, u)
    assert support_issubset(covered_x, x_vars, fol)
    return covered_x


def _embed_as_implicants(f, px, fol):
    ax = {x: d['a'] for x, d in px.items()}
    bx = {x: d['b'] for x, d in px.items()}
    u = fol.let(ax, f)
    v = _orthotope_signleton(px, fol)
    return u & v


def _embed_as_implicants_naive(f, px, fol):
    """Return product representation of minterms."""
    x_as_ab = {x: dict(a=x, b=x) for x in px}
    varmap = _parameter_varmap(px, x_as_ab)
    r = _orthotope_eq(varmap, fol)
    return fol.exist(x_as_ab, r & f)


# slower than `_orthotope_signleton`
# needs `from omega.symbolic import fol as _fol`
# @profile
def _orthotope_signleton_wo_parsing(px, fol):
    """Return BDD that orthotope contains single point."""
    a_b = {d['a']: d['b'] for d in px.values()}
    bitmap = _fol._refine_renaming(a_b, fol.vars)
    bdd = fol.bdd
    r = bdd.true
    for b1, b2 in bitmap.items():
        u = bdd.var(b1)
        v = bdd.var(b2)
        u = bdd.apply('<=>', u, v)
        r &= u
    r_ = _orthotope_signleton(px, fol)
    assert r == r_, (r, r_)
    return r


def _orthotope_signleton(px, fol):
    """Return BDD that orthotope contains single point."""
    s = stx.conj(
        '({a} = {b})'.format(
            a=d['a'], b=d['b'])
        for x, d in px.items())
    r = fol.add_expr(s)
    return r


def _orthotope_nonempty(abx, fol):
    """Return condition that orthotope be non-empty."""
    s = stx.conj(
        '({a} <= {b})'.format(
            a=d['a'], b=d['b'])
        for x, d in abx.items())
    r = fol.add_expr(s)
    return r


def _orthotope_contains_x(abx, fol):
    """Return `x \in concretization(abx)`."""
    s = stx.conj((
        '({a} <= {x}) /\ '
        '({x} <= {b})').format(
            x=x, a=d['a'], b=d['b'])
        for x, d in abx.items())
    r = fol.add_expr(s)
    return r


def _orthotope_subseteq(varmap, fol):
    r"""Return `ab \subseteq uv`.

    This is the partial order defined by the subset relation.
    In the general formulation `\sqsubseteq`.
    """
    s = stx.conj((
        '({u} <= {a}) /\ '
        '({b} <= {v})').format(a=a, b=b, u=u, v=v)
            for (a, b), (u, v) in varmap.items())
    r = fol.add_expr(s)
    return r


def _orthotope_eq(varmap, fol):
    """Return `ab = uv`."""
    s = stx.conj((
        '({a} = {u}) /\ '
        '({b} = {v})').format(a=a, b=b, u=u, v=v)
        for (a, b), (u, v) in varmap.items())
    r = fol.add_expr(s)
    return r


def _orthotopes_intersect(varmap, fol):
    """Return `ab \cap uv # \emptyset`.

    Equivalent to

    \E x:  /\ x \in concretization(ab)
           /\ x \in concretization(uv)

    The representation of orthotopes as products of
    intervals allows for a direct construction that
    avoids quantification over `x`.
    """
    # disjoint intervals in at least one dimension
    s = stx.disj((
        '({b} < {u}) \/ '
        '({v} < {a})').format(a=a, b=b, u=u, v=v)
            for (a, b), (u, v) in varmap.items())
    r = fol.add_expr(s)
    return ~ r


def plot_orthotopes(u, abx, axvars, fol, ax):
    """Plot a polytope for each orthotope in `u`.

    @param axvars: `list` that defines which variable
        spans each dimension of the plot.
    """
    try:
        import polytope as poly
    except ImportError:
        raise ImportError(
            '`orthotopes` failed to import `polytope`.\n'
            'No plotting of orthotopes.')
    c = _orthotopes_iter(u, fol)
    eps = 0.1
    cycol = cycle('bgrcmk')
    for product in c:
        x, y = axvars
        a_x = abx[x]['a']
        b_x = abx[x]['b']
        a_y = abx[y]['a']
        b_y = abx[y]['b']
        xmin = product[a_x]
        xmax = product[b_x]
        ymin = product[a_y]
        ymax = product[b_y]
        # if a = b add a small amount
        if xmin == xmax:
            xmin -= eps
            xmax += eps
        if ymin == ymax:
            ymin -= eps
            ymax += eps
        size = [[xmin, xmax], [ymin, ymax]]
        p = poly.box2poly(size)
        color = next(cycol)
        p.plot(ax=ax, color=color, alpha=0.5)


def plot_points(u, keys, fol, ax, **kw):
    """Plot in 2D the integer assignments in a BDD."""
    for d in fol.pick_iter(u, care_vars=keys):
        plot(d, keys, ax=ax, **kw)


def plot(d, keys, ax, **kw):
    """The missing plot function for named coordinates."""
    t = tuple(d[k] for k in keys)
    ax.plot(*t, **kw)


def dumps_cover(
        cover, f, care, fol,
        latex=False,
        show_dom=False,
        show_limits=False):
    """Return disjunction of orthotopes in `cover`, one per line.

    @param latex: use `pf.sty` commands
    @param show_dom: if `care` implies type hints,
        then conjoin type hints (`fol.vars[var]['dom']`)
    @param show_limits: conjoin limits of  bitfield values

    @rtype: `str`
    """
    x_vars, px, _, _ = _setup_aux_vars(f, care, fol)
    c = list()
    if show_limits:
        r = _list_limits(x_vars, fol.vars)
        c.extend(r)
    show_dom = show_dom and _care_implies_type_hints(f, care, fol)
    if show_dom:
        r = _list_type_hints(x_vars, fol.vars)
        c.extend(r)
    else:
        log.info(
            'type hints omitted (care does not imply them)')
    r = _list_orthotope_expr(
        cover, px, fol, use_dom=show_dom)
    s = _vertical_op(r, op='or', latex=latex)
    c.append(s)
    n_expr = len(r)
    if care != fol.true:
        c.append('care expression')
    s = _vertical_op(c, op='and', latex=latex)
    # could add option to find minimal cover for care too
    return s


def _vertical_op(c, latex=False, op='and'):
    """Return TLA conjunction with one conjunct per line."""
    assert op in {'and', 'or'}, op
    if not c:
        r = 'TRUE' if op == 'and' else 'FALSE'
        return r
    # singleton ?
    if len(c) == 1:
        return c[0]
    if latex:
        pref = '  '
        nl = r' \\' + '\n'
    else:
        pref = '/\\' if op == 'and' else '\/'
        nl = '\n'
    r = list()
    for s in c:
        t = s.split('\n')
        t[0] = ' {p} {first}'.format(p=pref, first=t[0])
        e = '\n    '.join(t)
        r.append(e)
    r = nl.join(r)
    env = 'conj' if op == 'and' else 'disj'
    if latex:
        r = ('\\begin{' + env + '}\n' + r +
             '\n\\end{' + env + '}')
    return r


def _list_orthotope_expr(
        cover, px, fol,
        simple=False,
        use_dom=False):
    """Return `list` of `str`, each an orthotope in `cover`.

    @param simple: if `True`, then return expression
        that can be parsed by `fol.add_expr`.
    @param use_dom: omit conjuncts that contain dom of var
        assumes that `|= care => type_hints`
    """
    xp = _map_parameters_to_vars(px)
    support = fol.support(cover)
    keys = {xp[k] for k in support}
    keys = natsort.natsorted(keys)
    c = _orthotopes_iter(cover, fol)
    r = list()
    for product in c:
        w = list()
        for x in keys:
            a = px[x]['a']
            b = px[x]['b']
            a = product[a]
            b = product[b]
            _check_type_hint(a, b, fol.vars[x], x)
            # can `x` be ignored ?
            if use_dom:
                dom = fol.vars[x]['dom']
                a, b = _clip_subrange((a, b), dom, x)
            if a is None and b is None:
                continue
            if a == b:
                s = '({x} = {a})'
            elif simple:
                s = '({a} <= {x}) /\ ({x} <= {b})'
            else:
                # precise even in absence of limits/dom
                s = '({x} \in {a} .. {b})'
            s = s.format(x=x, a=a, b=b)
            w.append(s)
        s = ' /\ '.join(w)
        if not s:
            s = 'TRUE'
        r.append(s)
    r = natsort.natsorted(r)  # reproducable vertical listing
    return r


def _clip_subrange(ab, dom, x):
    """Return `ab` clipped to `dom`."""
    a, b = ab
    u, v = dom
    # assert not disjoint ranges
    assert a <= v and b >= u, (ab, dom, x)
    a = max(a, u)
    b = min(b, v)
    if a == u and v == b:
        a, b = None, None
    return a, b


def _check_type_hint(a, b, hint, var):
    """Raise `AssertionError` and log warnings."""
    if a > b:
        raise AssertionError((
            'Empty orthotope interval `{a} .. {b}` for '
            'variable "{var}".').format(
                a=a, b=b, var=var))
    dom = hint['dom']
    limits = _bitfield_limits(hint)
    if a > dom[1] or b < dom[0]:
        log.warning((
            'Interval `a .. b = {a} .. {b}` is disjoint from '
            'type hint `dom = {dom[0]} .. {dom[1]}` for '
            'variable "{var}".\n'
            'Use type hint `dom` as care set.\n').format(
                a=a, b=b, dom=dom, var=var))
    # `a <= dom[0]` should imply `a = limits[0]`,
    # because otherwise only possible if some point
    # outside type hint matters, preventing prime to
    # extend to the limits of the bitfield
    if a <= dom[0] and a > limits[0]:
        log.warning((
            'a = {a} not in interior of type hint '
            '`dom = {dom[0]} .. {dom[1]}` but unequal to '
            'low of `limits = {limits[0]} .. {limits[1]}` '
            'for variable "{var}".\n'
            'Use type hint as care set.\n').format(
                a=a, dom=dom, limits=limits, var=var))
    if b >= dom[1] and b < limits[1]:
        log.warning((
            'b = {b} not in interior of type hint '
            '`dom = {dom[0]} .. {dom[1]}` but unequal to '
            'high of `limits = {limits[0]} .. {limits[1]}` '
            'for variable "{var}".\n'
            'Use type hint as care set.\n').format(
                b=b, dom=dom, limits=limits, var=var))


def _care_implies_type_hints(f, care, fol):
    """Return `True` if `|= care => type_hints`."""
    vrs = joint_support([f, care], fol)
    type_hints = _conjoin_type_hints(vrs, fol)
    u = type_hints | ~ care
    return u == fol.true


def _f_implies_care(f, care, fol):
    """Return `True` if `|= f => care`."""
    return (care | ~ f) == fol.true


def _list_type_hints(variables, table):
    """Return `list` of set containment constraints.

    These are the high-level type invariant,
    as defined by the type hints (`"dom"`) in `table`.
    """
    assert variables, variables
    r = list()
    keys = natsort.natsorted(variables)
    for x in keys:
        dom = table[x]['dom']
        s = _format_range(x, *dom)
        r.append(s)
    return r


def _list_limits(vrs, table):
    """Return `list` of bitfield limits.

    Each limit has the form `x \in a .. b`

    @param table: must be bitblasted
    """
    assert vrs, vrs
    r = list()
    keys = natsort.natsorted(vrs)
    for x in keys:
        limits = _bitfield_limits(table[x])
        s = _format_range(x, *limits)
        r.append(s)
    return r


def _bitfield_limits(hint):
    """Return extremal integer values of bitfield."""
    width = hint['width']
    if hint['signed']:
        n = width - 1
        limits = (- 2**n, 2**n - 1)
    else:
        limits = (0, 2**width - 1)
    return limits


def _conjoin_type_hints(vrs, fol):
    """Return conjunction of type hints for `vrs` as BDD."""
    r = list()
    for var in vrs:
        hints = fol.vars[var]
        a, b = hints['dom']
        s = '({a} <= {var}) /\ ({var} <= {b})'.format(
            a=a, b=b, var=var)
        r.append(s)
    u = fol.add_expr(stx.conj(r))
    return u


def _format_range(var, a, b):
    """Return string for set containment `var \in a .. b`."""
    return r'{var} \in {a} .. {b}'.format(
        var=var, a=a, b=b)


def _orthotopes_iter(u, fol):
    """Return iterator over orthotopes."""
    if u == fol.false:
        log.info('empty set')
    c = fol.pick_iter(u)
    return c


def _setup_aux_vars(f, care, fol):
    """Add and return auxiliary variables.

    No BDD operations other than `support` are invoked.

    Returns:

    - `x_vars`: set of variable names in
        `support(f) \/ support(care)`
    - `px`: map var name to `dict` of indexed parameters
    - `qx`: similar for var copies
    - `p_to_q`: `dict` that maps parameters to their copies

    For example:

    ```
    x_vars = {'x', 'y'}
    px = dict(
        x=dict(a='a_x', b='b_x'),
        y=dict(a='a_y', b='b_y'))
    qx = dict(
        x=dict(a='u_x', b='v_x'),
        y=dict(a='u_y', b='v_y'))
    p_to_q = dict(
        a_x='u_x', b_x='v_x',
        a_y='u_y', b_y='v_y')
    ```

    @return x_vars, px, qx, p_to_q
    """
    assert f != fol.false
    assert care != fol.false
    assert not (f == fol.true and care == fol.true)
    x_vars = joint_support([f, care], fol)
    assert x_vars, x_vars
    # aux vars for orthotope representation
    params = dict(pa='a', pb='b', qa='u', qb='v')
    p_dom = _parameter_table(
        x_vars, fol.vars, a=params['pa'], b=params['pb'])
    q_dom = _parameter_table(
        x_vars, fol.vars, a=params['qa'], b=params['qb'])
    p_dom = _add_prime_like_too(p_dom)
    q_dom = _add_prime_like_too(q_dom)
    common = x_vars.intersection(p_dom)
    assert not common, common
    common = x_vars.intersection(q_dom)
    assert not common, common
    # works even if subclass of `Context`
    # overrides `add_vars`
    fol.add_vars(p_dom)
    fol.add_vars(q_dom)
    px = _parameter_variables(x_vars, a=params['pa'], b=params['pb'])
    qx = _parameter_variables(x_vars, a=params['qa'], b=params['qb'])
    assert set(px) == set(qx), (px, qx)
    p_to_q = _renaming_between_parameters(px, qx)
    log.debug('x vars: {x_vars}'.format(x_vars=x_vars))
    return x_vars, px, qx, p_to_q


def _parameter_table(x, table, a, b):
    """Return symbol table that defines parameters.

    Supports integer-valued variables only.
    Represent Boolean-valued as 0..1-valued variables.
    """
    assert x, x
    d = dict()
    for xj in x:
        dtype = table[xj]['type']
        assert dtype in ('int', 'saturating'), dtype
        dom = table[xj]['dom']
        name = _replace_prime(xj)
        aj = '{a}_{v}'.format(a=a, v=name)
        bj = '{b}_{v}'.format(b=b, v=name)
        d[aj] = dict(type='int', dom=dom, owner=VAR_OWNER)
        d[bj] = dict(type='int', dom=dom, owner=VAR_OWNER)
        assert "'" not in aj, aj
        assert "'" not in bj, bj
    assert len(d) == 2 * len(x), d
    return d


def _parameter_variables(x_vars, a, b):
    """Return `dict` that maps each var x to a_x, b_x."""
    d = dict()
    for x in x_vars:
        name = _replace_prime(x)
        a_x = '{a}_{v}'.format(v=name, a=a)
        b_x = '{b}_{v}'.format(v=name, b=b)
        d[x] = dict(a=a_x, b=b_x)
    return d


def _map_parameters_to_vars(px):
    """Return map `{a: x, b: x, ...}`."""
    d = {d['a']: k for k, d in px.items()}
    d.update((d['b'], k) for k, d in px.items())
    return d


def _collect_parameters(px):
    """Return `set` of parameters from `px`."""
    c = set()
    c.update(d['a'] for d in px.values())
    c.update(d['b'] for d in px.values())
    assert len(c) == 2 * len(px), (c, px)
    return c


def _parameter_varmap(px, qx):
    """Return map `{(a, b): (u, v), ... }`."""
    assert set(px) == set(qx), (px, qx)
    d = dict()
    for x in px:
        a = px[x]['a']
        b = px[x]['b']
        u = qx[x]['a']
        v = qx[x]['b']
        d[(a, b)] = (u, v)
    return d


def _renaming_between_parameters(px, qx):
    """Return map `{a: u, b: v, ... }`."""
    assert set(px) == set(qx), (px, qx)
    d = dict()
    for x in px:
        a = px[x]['a']
        b = px[x]['b']
        u = qx[x]['a']
        v = qx[x]['b']
        d[a] = u
        d[b] = v
    return d


def _replace_prime(var):
    """Replace postfix prime with "_p"

    To avoid parsing a parameter's name as if it is
    two names with an operator in the middle.
    This case arises for parameters that associated to
    primed variables.

    For example, when computing a minimal cover for
    an action.
    """
    if not stx.isprimed(var):
        assert "'" not in var, var
        return var
    assert stx.isprimed(var), var
    unprimed = stx.unprime(var)
    # `'` even in the middle would split it when parsing
    assert "'" not in unprimed, unprimed
    var_p = '{unprimed}_p'.format(unprimed=unprimed)
    assert "'" not in var_p, var_p
    return var_p


def _add_prime_like_too(table):
    """Return new table of primed and unprimed vars.

    All variables in `table` should be unprimed.

    @type table: `dict`
    @rtype: `dict`
    """
    t = dict()
    for var, d in table.items():
        assert not stx.isprimed(var), var
        assert 'bitnames' not in d, d  # precaution
        pvar = _prime_like(var)
        t[var] = dict(d)
        t[pvar] = dict(d)
    return t


def _prime_like(var):
    return '{var}_cp'.format(var=var)


class _BranchAndBound(object):
    """A data structure that stores useful values.

    It helps avoid passing 10 arguments in each
    function call during the recursion.
    Attributes:

    - `lower_bound`: global lower bound
    - `upper_bound`: global upper bound (feasible)
    """

    def __init__(
            self, p_leq_q, p_leq_u, u_leq_p,
            p_eq_q, p_to_q, px, qx, fol):
        self._lower_bound = None
        self._upper_bound = None
        self.best_cover = None  # found so far
        self.p_leq_q = p_leq_q
        self.p_leq_u = p_leq_u
        self.u_leq_p = u_leq_p
        self.p_eq_q = p_eq_q
        self.p_to_q = p_to_q
        self.px = px
        self.qx = qx
        self.fol = fol

    def _assert_invariant(self, lower=None, upper=None):
        """Raise `AssertionError` if lower > upper bound."""
        if lower is None:
            lower = self._lower_bound
        if upper is None:
            upper = self._upper_bound
        if lower is None or upper is None:
            return
        assert lower <= upper, (lower, upper)

    @property
    def lower_bound(self):
        return self._lower_bound

    @lower_bound.setter
    def lower_bound(self, c):
        assert c >= 0, c
        # only initialize global lower bound
        assert self._lower_bound is None, self._lower_bound
        self._assert_invariant(lower=c)
        self._lower_bound = c

    @property
    def upper_bound(self):
        return self._upper_bound

    @upper_bound.setter
    def upper_bound(self, c):
        assert c > 0, c
        self._assert_invariant(upper=c)
        if self._upper_bound is None:
            log.info(
                'initialized upper bound to {c}'.format(
                    c=c))
        elif c < self._upper_bound:
            log.info((
                'improved upper bound from '
                '{old} to {new}').format(
                    old=self._upper_bound,
                    new=c))
        self._upper_bound = c
