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

import humanize
import natsort
from omega.logic import syntax as stx
from omega.symbolic.prime import support_issubset
from omega.symbolic.prime import joint_support
from omega.symbolic import orthotopes as lat
from omega.symbolic import _type_hints as tyh
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
    prm = lat.setup_aux_vars(f, care, fol)
    lat.setup_lattice(prm, fol)
    # covering problem
    fcare = f | ~ care
    # the slack is introduced by having more primes
    # (those for `fcare`) to cover the same minterms (`f`)
    x = lat.embed_as_implicants(f, prm, fol)
    y = lat.prime_implicants(fcare, prm, fol)
    bab = _BranchAndBound(prm, fol)
    # initialize upper bound
    bab.upper_bound = _upper_bound(
        x, y, prm.p_leq_q, prm.p_to_q, fol)
    # assert covers(bab.best_cover, f, prm, fol)
    cover, _ = _traverse(x, y, path_cost, bab, fol)
    if cover is None:
        cover, _ = _some_cover(x, y, prm.p_leq_q, p_to_q, fol)
    assert cover is not None
    cover = unfloors(cover, y, fol, bab)
    assert_is_a_cover_from_y(
        cover, y, f, prm, fol)
    low = care & ~ f
    assert _none_covered(cover, low, prm, fol)
    log.info('==== branching ==== ')
    return cover


def _minimize_two_managers(f, care, fol):
    """Optimized version of `minimize` for large problems."""
    if not _care_implies_type_hints(f, care, fol):
        log.warning('care set should imply type hints')
    if not _f_implies_care(f, care, fol):
        log.warning('f should imply care set')
    if (f | ~ care) == fol.true:
        log.warning('f covers care set, so trivial cover')
    log.info('---- branching ----')
    path_cost = 0.0
    # x_vars, px, qx, p_to_q
    prm = lat.setup_aux_vars(f, care, fol)
    # manager where optimization happens
    fol_2 = type(fol)()
    fol_2.add_vars(fol.vars)
    # x (to be covered)
    log.info('embed implicants')
    x = lat.embed_as_implicants(f, prm, fol)
    x = fol.copy(x, fol_2)
    # covering problem
    fcare = f | ~ care
    lat.setup_lattice(prm, fol_2)
    # y (to use in cover)
    log.info('primes')
    fcare_2 = fol.copy(fcare, fol_2)
    y = lat.prime_implicants(fcare_2, prm, fol_2)
    del fcare_2
    bab = _BranchAndBound(prm, fol_2)
    # initialize upper bound
    bab.upper_bound = _upper_bound(
        x, y, prm.p_leq_q, prm.p_to_q, fol_2)
    # assert _covers(bab.best_cover, f, prm, fol_2)
    log.info('traverse')
    cover, _ = _traverse(x, y, path_cost, bab, fol_2)
    if cover is None:
        cover, _ = _some_cover(x, y, prm.p_leq_q, prm.p_to_q, fol_2)
    assert cover is not None
    cover = unfloors(cover, y, fol_2, bab)
    log.info('==== branching ==== ')
    del fcare, prm, bab
    cover = fol_2.copy(cover, fol)
    return cover


def _assert_correct_cover(cover, f, care, fol):
    """Raise `AssertionError` if `cover` not of `f`."""
    prm = lat.setup_aux_vars(f, care, fol)
    # in implicant space
    low = care & ~ f
    assert _none_covered(cover, low, prm, fol)
    # in concrete space
    g = _concretize_implicants(cover, prm, fol)
    assert (g & care) == (f & care)


def unfloors(cover, y, fol, bab):
    """Return a minimal cover using elements from y.

    This operation inverts the effect of `Floors`,
    which can result in elements that are below those in `y`.

    This implementation is enumerative.
    There is no loss of efficiency, because computing
    an upper bound takes at least as long as enumerating
    a minimal cover. After all, we compute a minimal cover
    in order to print it, so it will be enumerated.
    """
    y_cover = fol.false
    yq = fol.let(bab.p_to_q, y)
    p_leq_y = bab.p_leq_q & yq
    for dz in fol.pick_iter(cover):
        # any min cover is an antichain,
        # so `dz` must be specific implicant
        assert set(dz) == bab.p_vars, dz
        over = fol.let(dz, p_leq_y)  # ThoseOver(Y, z)
        dy = fol.pick(over)
        # y is a set of primes, so an antichain,
        # so `dy` must be a specific implicant,
        # not a partial assignment
        assert set(dy) == bab.q_vars, dy
        y = fol.assign_from(dy)
        y_cover |= y
    y_cover = fol.let(bab.q_to_p, y_cover)
    return y_cover


def _traverse(x, y, path_cost, bab, fol):
    """Compute cyclic core and terminate, prune, or recurse."""
    log.info('\n\n---- traverse ----')
    t0 = time.time()
    xcore, ycore, essential = _cyclic_core_fixpoint(
        x, y, bab, fol)
    _print_cyclic_core(
        x, y, xcore, ycore, essential,
        t0, bab.prm, fol)
    # C_left.path =
    #     C.path + 1  (* already from `_branch` *)
    # C_left.lower =
    #     + Cardinality(essential_left)  (* `_cost` *)
    #     + LowerBound(core_left)  (* `lb` below *)
    #
    # C_right.path =
    #     C.path  (* already from `_branch` *)
    # C_right.lower =
    #     + Cardinality(essential_right)
    #     + LowerBound(core_right)
    cost_ess = _cost(essential, bab.prm, fol)
    core_lb = _lower_bound(
        xcore, ycore, bab.p_leq_q, bab.p_to_q, fol)
    sub_lb = cost_ess + core_lb
    branch_lb = path_cost + sub_lb
    if xcore == fol.false:
        assert core_lb == 0, core_lb
        bab.upper_bound = branch_lb
        log.info('terminal case (empty cyclic core)\n'
                 '==== traverse ====\n')
        return essential, sub_lb
    # set global lower bound only once at the top
    # because farther below in the search tree the
    # lower bounds are local, not global
    if bab.lower_bound is None:
        log.info(
            'global lower bound: {lb}'.format(lb=branch_lb))
        bab.lower_bound = branch_lb
    # prune
    # C_left.path + C_left.lower >= global_upper_bound ?
    # C_right.path + C_right.lower >= global_upper_bound ?
    if branch_lb >= bab.upper_bound:
        log.info('prune\n==== traverse ====\n')
        return None, sub_lb
    assert xcore != fol.false
    assert ycore != fol.false
    # branch
    longer_path_cost = path_cost + cost_ess
    r = _branch(xcore, ycore, longer_path_cost, bab, fol)
    # both branches pruned ?
    if r is None:
        log.info('both branches pruned\n'
                 '==== traverse ====\n')
        return None, sub_lb
    cover = r | essential
    log.info('==== traverse ====\n')
    return cover, sub_lb


def _branch(x, y, path_cost, bab, fol):
    log.info('\n\n---- branch ----')
    d = fol.pick(y)
    assert set(d) == bab.p_vars, d  # must be specific implicant
        # This condition follows because Y is an antichain when we pick.
    log.info('picked branching y: {d}'.format(d=d))
    y_branch = fol.assign_from(d)
    ynew = y & ~ y_branch
    assert ynew != y
    # r(p) == p <= y_branch
    dq = {bab.p_to_q[k]: v for k, v in d.items()}
    r = fol.let(dq, bab.p_leq_q)  # those x under y_branch
    x_minus_y = x & ~ r
    assert x_minus_y != x  # must prove always the case
    log.info('left branch')
    e0, left_lb = _traverse(
        x_minus_y, ynew, path_cost + 1, bab, fol)
    # pruning with left lower bound (Thm.7 [Coudert 1994])
    if path_cost + left_lb >= bab.upper_bound:
        log.info(
            'prune both left and right branches\n'
            '==== branch ====\n')
        assert e0 is None, e0
        return None
    log.info('right branch')
    e1, _ = _traverse(x, ynew, path_cost, bab, fol)
    # pick cheaper
    cost_0 = _cost(e0, bab.prm, fol)
    cost_1 = _cost(e1, bab.prm, fol)
    if cost_0 < cost_1:
        # can be reached only if `e0 != None`
        assert e0 is not None, e0
        e = e0 | y_branch
    else:
        e = e1
    log.info('==== branch ====\n')
    return e


def _cost_enumerative(u, prm, fol):
    """Compute cost of cover `u` by enumerating it."""
    if u is None:
        return float('inf')
    eq = prm.eq
    cover = list()
    params = prm.p_vars
    for p in fol.pick_iter(u, params):
        # equal to existing ?
        r = fol.false
        for w in cover:
            w.update(p)
            r = fol.let(w, eq)
            if r == fol.true:
                break
        # skip if same prime
        if r == fol.true:
            continue
        cover.append(p)
    n = len(cover)
    print('enumerative cost: {n}'.format(n=n))
    count = fol.count(u)
    assert n <= count, (n, count)
    if n < count:
        print('Cost(u) < fol.count(u)')
    return n


def _cost(u, prm, fol):
    """Return numerical cost of cover `u`.

    ASSUME that no two assignments that satisfy `u`
    represent the same implicant (no duplicates).
    """
    if u is None:
        return float('inf')
    # cost of each implicant = 1
    # cost of a cover = number of implicants it contains
    assert _no_duplicate(u, prm, fol)
    assert support_issubset(u, prm.p_vars, fol)
    n = fol.count(u)
    return n


def _no_duplicate(u_p, prm, fol):
    """Return `True` if no doubly parameterized implicant in `u_p`."""
    assert support_issubset(u_p, prm.p_vars, fol)
    # checks that parameterization restricted to `u` is injective
    # \A p, q \in u:  eq(p, q) => (p = q)
    u_q = fol.let(prm.p_to_q, u_p)
    eq_implicants = prm.p_eq_q
    eq_parameters = _equality_of_pairs(prm.p_to_q.items(), fol)
    bound = u_p & u_q
    r = ~ bound | ~ eq_implicants | eq_parameters
    r = fol.forall(prm.p_vars | prm.q_vars, r)
    return r == fol.true


def _equality_of_pairs(pairs, fol):
    """Return `<< a1, a2, ... >> = << b1, b2, ... >>`.

    @param pairs: iterable of 2-tuples of identifiers
    """
    s = stx.conj(
        '({a} = {b})'.format(a=a, b=b)
        for a, b in pairs)
    r = fol.add_expr(s)
    return r


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
    prm = lat.setup_aux_vars(f, care, fol)
    lat.setup_lattice(prm, fol)
    fcare = ~ care | f
    bab = _BranchAndBound(prm, fol)
    # covering problem
    x = lat.embed_as_implicants(f, prm, fol)
    y = lat.prime_implicants(fcare, prm, fol)
    # assert problem is feasible
    assert x != fol.false
    assert y != fol.false
    assert _covers(y, f, prm, fol)
    xcore, ycore, essential = _cyclic_core_fixpoint(
        x, y, bab, fol)
    if xcore == fol.false:
        assert _covers(essential, f, prm, fol)
    _print_cyclic_core(
        x, y, xcore, ycore, essential,
        t0, bab.prm, fol)
    return xcore, ycore, essential


def _print_cyclic_core(
        x, y, xcore, ycore, essential,
        t0, prm, fol):
    """Print results of cyclic core computation.

    Assert support and covering properties.
    """
    if log.getEffectiveLevel() > logging.INFO:
        return
    # assert
    if essential != fol.false:
        assert support_issubset(essential, prm.p_vars, fol)
    if xcore != fol.false:
        assert support_issubset(xcore, prm.p_vars, fol)
    if ycore != fol.false:
        assert support_issubset(ycore, prm.p_vars, fol)
    # print
    m = fol.count(x)
    n = fol.count(y)
    log.info((
        '(x={m}, y={n}) implicants of '
        'covering problem').format(
            m=humanize.intcomma(m),
            n=humanize.intcomma(n)))
    m = fol.count(xcore)
    n = fol.count(ycore)
    log.info((
        '(x={m}, y={n}) implicants after '
        'removing essential elements').format(
            m=humanize.intcomma(m),
            n=humanize.intcomma(n)))
    n = fol.count(essential)
    log.info('{n} primes are essential'.format(
        n=humanize.intcomma(n)))
    t1 = time.time()
    dt = t1 - t0
    log.info('cyclic core took {dt}'.format(
        dt=humanize.naturaldelta(dt)))


def _cyclic_core_fixpoint(x, y, bab, fol):
    """Return cyclic core and essential elements."""
    log.debug('\n\n---- cyclic core fixpoint ----')
    assert x in fol.bdd, x
    assert y in fol.bdd, y
    assert support_issubset(x, bab.p_vars, fol)
    assert support_issubset(y, bab.p_vars, fol)
    # compute
    essential = fol.false
    xold, yold = None, None
    i = 0
    while x != xold or y != yold:
        log.debug('starting iteration {i}'.format(i=i))
        t0 = time.time()
        xold, yold = x, y
        x = _max_transpose(x, y, bab, fol, signatures=True)
        e = x & y
        x = x & ~ e
        y = y & ~ e
        essential |= e
        y = _max_transpose(x, y, bab, fol)
        t1 = time.time()
        dt = t1 - t0
        log.debug('iteration {i} took {dt:1.2f} sec'.format(
            i=i, dt=dt))
        i += 1
    _assert_fixpoint(
        x, y, xold, yold, essential, bab.p_vars, fol)
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
                   bab, fol, signatures=False):
    """Maximal transposed primes or signatures.

    (max tau_Y(X) or max tau_X(Y))

    @param signatures: if `True`, then transpose signatures,
        otherwise primes.

    Requires that `p, p', q` be in `fol.vars` and
    be refined by the same number of bits each.
    """
    log.info('---- max transpose ----')
    assert support_issubset(p_is_prime, bab.p_vars, fol)
    assert support_issubset(p_is_signature, bab.p_vars, fol)
    # compute
    u = _floor(
        p_is_signature, p_is_prime,
        bab, fol, signatures=signatures)
    r = _maxima(u, bab, fol)
    assert support_issubset(r, bab.p_vars, fol)
    log.info('==== max transpose ====')
    return r


def _floor(p_is_signature, p_is_prime,
           bab, fol, signatures=False):
    """Transpose primes (tau_X(Y)) or signatures (tau_Y(X)).

    Floor(S) = Join(S)
    Ceil(S) = Meet(S)

    @param p_is_prime: some primes, function of `p`
    @param p_is_signature: function of `p`
    @param signatures: if `True`, then transpose signatures,
        otherwise primes.
    """
    log.info('---- tranpose ----')
    p_leq_u = bab.p_leq_u
    u_leq_p = bab.u_leq_p
    if signatures:
        p_is_signature, p_is_prime = p_is_prime, p_is_signature
        u_leq_p, p_leq_u = p_leq_u, u_leq_p
    # assert
    assert support_issubset(p_is_prime, bab.p_vars, fol)
    assert support_issubset(p_is_signature, bab.p_vars, fol)
    # p' used as u
    u_is_signature = fol.let(bab.p_to_u, p_is_signature)
    # same coverage
    p_like_q = _contains_covered(
        u_is_signature, u_leq_p, bab, fol)
    u_like_q = fol.let(bab.p_to_u, p_like_q)
    # u_is_prime = fol.let(p_to_u, p_is_prime)
    q_is_prime = fol.let(bab.p_to_q, p_is_prime)
    #
    r = ~ u_like_q | p_leq_u
    r = fol.forall(bab.u_vars, r)
    r &= p_like_q
    r &= q_is_prime
    r = fol.exist(bab.q_vars, r)
    '''
    q = ', '.join(iter(p_to_q.values()))
    u = ', '.join(iter(p_to_u.values()))
    s = (
        '\E {q}:  {q_is_prime} /\ {p_like_q} /\ '
        '    \A {u}:  {u_like_q} => {p_leq_u}').format(
            q=q,
            u=u,
            q_is_prime=q_is_prime,
            p_like_q=p_like_q,
            u_like_q=u_like_q,
            p_leq_u=p_leq_u)
    r = fol.add_expr(s)
    '''
    assert support_issubset(r, bab.p_vars, fol)
    log.info('==== tranpose ====')
    return r


def _contains_covered(u_is_signature, u_leq_p, bab, fol):
    """Return primes that cover all signatures under prime.

    CAUTION: keep `u_leq_p` in the arguments,
    because the function `_floor` swaps with `p_leq_u`
    before calling `_contains_covered`.

    In the proof, this operator is equivalent to:
        `IsAbove(p, ThoseUnder(u_is_signature, q, Leq))`

    @param signatures: function of `u`
    """
    log.info('---- contains covered ----')
    # assert
    pq_vars = bab.p_vars.union(bab.q_vars)
    pu_vars = bab.p_vars.union(bab.u_vars)
    assert support_issubset(u_is_signature, bab.u_vars, fol)
    assert support_issubset(u_leq_p, pu_vars, fol)
    # compute
    u_leq_q = fol.let(bab.p_to_q, u_leq_p)
    r = u_is_signature & u_leq_q
    r = ~ r | u_leq_p
    r = fol.forall(bab.u_vars, r)
    '''
    uvars = ', '.join(bab.u_vars)
    s = (
        '\A {uvars}:  '
        '    ({sig_u} /\ {u_leq_q}) '
        '        => {u_leq_p}').format(
        uvars=uvars,
        sig_u=u_is_signature,
        u_leq_q=u_leq_q,
        u_leq_p=u_leq_p)
    r = fol.add_expr(s)
    '''
    assert support_issubset(r, pq_vars, fol)
    log.info('==== contains covered ====')
    return r


def _maxima(u, bab, fol):
    """Return maximal elements of `u` wrt `bab.p_leq_q`.

    @param u: function of `bab.p_vars`
    """
    assert support_issubset(u, bab.p_vars, fol)
    v = fol.let(bab.p_to_q, u)
    #
    r = v & bab.p_leq_q
    r = ~ r | bab.p_eq_q
    r = fol.forall(bab.q_vars, r)
    r &= u
    '''
    q = ', '.join(bab.q_vars)
    s = (
        '{u} /\ '
        '\A {q}:  ({v} /\ {p_leq_q}) => ({p_eq_q})').format(
            u=u,
            v=v,
            p_leq_q=bab.p_leq_q,
            p_eq_q=bab.p_eq_q,
            q=q)
    r = fol.add_expr(s)
    '''
    assert support_issubset(r, bab.p_vars, fol)
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
    assert _cover_refines(x, yq, p_leq_q, p, q, fol)
    rem = x
    z = fol.false
    k = 0
    n = fol.count(rem)
    assert n >= 0, n
    while rem != fol.false:
        x0 = fol.pick(rem)
        assert set(x0) == p, x0
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
        assert set(x0) == p, x0
        # ys that cover x0
        #
        # r(q) == /\ x0 <= q
        #         /\ y(q)
        r = yq & fol.let(x0, p_leq_q)
        y0 = fol.pick(r)
        assert set(y0) == q, y0
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


def _none_covered(
        cover_p, f, prm, fol):
    """Return `True` if `cover_p` covers no minterm in `f`.

    Arguments similar to `covers`.
    """
    fp = lat.embed_as_implicants(f, prm, fol)
    fq = fol.let(prm.p_to_q, fp)
    # \A p:  \/ ~ cover(p)
    #        \/ ~ \E q:  /\ f(q)
    #                    /\ Intersect(p, q)
    r = fq & lat.implicants_intersect(prm, fol)
    r = ~ fol.exist(prm.q_vars, r)
    r |= ~ cover_p
    r = fol.forall(prm.p_vars, r)
    return r == fol.true


def assert_is_a_cover_from_y(
        cover_p, y, f, prm, fol):
    """Assert `IsACoverFrom(cover_p, X, y, IsUnder)`

    The operator `IsACoverFrom` defined in the module
    `spec/MinCover.tla`.
    """
    assert (y | ~ cover_p) == fol.true, 'needs unfloors'
    assert _covers(cover_p, f, prm, fol)


def _covers(
        cover_p, f, prm, fol):
    """Return `True` if `cover_p` covers `f`.

    This is the operator `IsACover` defined in the
    module `spec/MinCover.tla`.

    @param cover_p: primes, repr as `p`
    @param f: elements to cover, repr as `x`
    """
    fp = lat.embed_as_implicants(f, prm, fol)
    cover_q = fol.let(prm.p_to_q, cover_p)
    # \A p:  \/ ~ f(p)
    #        \/ \E q:  cover(q) /\ (p <= q)
    r = cover_q & prm.p_leq_q
    r = fol.exist(prm.q_vars, r)
    r |= ~ fp
    r = fol.forall(prm.p_vars, r)
    return r == fol.true


def _covers_naive(cover_p, f, prm, fol):
    """Return `True` if `cover_p` covers `f`.

    Same as `covers`. Here the computation happens over
    the concrete variables (`x`), so it is less efficient.
    """
    assert support_issubset(f, prm.x_vars, fol)
    # concretize
    x_in_cover = _concretize_implicants(cover_p, prm, fol)
    covered = ~ f | x_in_cover
    return covered == fol.true


def _concretize_implicants(implicants_p, prm, fol):
    """Return covered set as function of `x`."""
    assert support_issubset(implicants_p, prm.p_vars, fol)
    # concretize
    x_in_p = lat.x_in_implicant(prm, fol)
    u = x_in_p & implicants_p
    covered_x = fol.exist(prm.p_vars, u)
    assert support_issubset(covered_x, prm.x_vars, fol)
    return covered_x


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
        show_limits=False,
        comment=True):
    """Return disjunction of orthotopes in `cover`, one per line.

    @param latex: use `pf.sty` commands
    @param show_dom: if `care` implies type hints,
        then conjoin type hints (`fol.vars[var]['dom']`)
    @param show_limits: conjoin limits of  bitfield values
    @param comment: if `True`, then list support of `f`, `cover`

    @rtype: `str`
    """
    prm = lat.setup_aux_vars(f, care, fol)
    c = list()
    if show_limits:
        r = tyh._list_limits(prm.x_vars, fol.vars)
        c.extend(r)
    show_dom = show_dom and _care_implies_type_hints(f, care, fol)
    if show_dom:
        r = tyh._list_type_hints(prm.x_vars, fol.vars)
        c.extend(r)
    else:
        log.info(
            'type hints omitted')
    r = lat.list_expr(
        cover, prm, fol, use_dom=show_dom, latex=latex)
    s = stx.vertical_op(r, op='or', latex=latex, spacing=2)
    c.append(s)
    if care != fol.true:
        c.append('care expression')
    s = stx.vertical_op(c, op='and', latex=latex)
    f_vars = fol.support(f)
    care_vars = fol.support(care)
    s_comment = (
        '(* `f` depends on:  {f_vars} *)\n'
        '(* `care` depends on:  {care_vars} *)\n'
        '(* The minimal cover is: *)').format(
            f_vars=_comma_sorted(f_vars),
            care_vars=_comma_sorted(care_vars))
    if comment:
        s = '{comment}\n{s}'.format(comment=s_comment, s=s)
    # could add option to find minimal cover for care too
    # postcondition
    r = lat.list_expr(
        cover, prm, fol, use_dom=show_dom)
    r = stx.disj(r)
    g = fol.add_expr(r)
    # ensure that `g` equals `f` inside `care`
    # `g` can be arbitrary outside of `care`
    assert (g & care) == (f & care), r
    return s


def _care_implies_type_hints(f, care, fol):
    """Return `True` if `|= care => type_hints`."""
    vrs = joint_support([f, care], fol)
    type_hints = tyh._conjoin_type_hints(vrs, fol)
    r = type_hints | ~ care
    if r != fol.true:
        vrs = _find_protruding_dimensions(care, type_hints, fol)
        s = ('`care => type_hints` fails '
             'for variables: {vrs}').format(
                vrs=_comma_sorted(vrs))
        log.warning(s)
    return r == fol.true


def _f_implies_care(f, care, fol):
    """Return `True` if `|= f => care`."""
    r = care | ~ f
    if r != fol.true:
        vrs = _find_protruding_dimensions(f, care, fol)
        s = ('`f => care` fails '
             'for variables: {vrs}').format(
                vrs=_comma_sorted(vrs))
        log.warning(s)
    return r == fol.true


def _find_protruding_dimensions(f, care, fol):
    """Return variables along which `f` violates `care`."""
    vrs = joint_support([f, care], fol)
    dims = set()
    for var in vrs:
        other_vars = vrs - {var}
        f_proj = fol.exist(other_vars, f)
        care_proj = fol.exist(other_vars, care)
        if (care_proj | ~ f_proj) != fol.true:
            dims.add(var)
    return dims


def _comma_sorted(c):
    """Return container `c` as comma separated list.

    The items are listed as sorted by `natsort`.
    """
    return ', '.join(natsort.natsorted(c))


class _BranchAndBound(object):
    """A data structure that stores useful values.

    It helps avoid passing 10 arguments in each
    function call during the recursion.
    Attributes:

    - `lower_bound`: global lower bound
    - `upper_bound`: global upper bound (feasible)
    - `p_leq_q`: partial order `p <= q`
        (anti-symmetry required: a quasi-order does not work.)
    - `p_to_q`: mapping from `p` to `q`
    - `u_leq_p`: partial order `u <= p`
    """

    def __init__(self, prm, fol):
        self._lower_bound = None
        self._upper_bound = None
        self.best_cover = None  # found so far
        # flat is better than nested
        self.p_vars = prm.p_vars
        self.q_vars = prm.q_vars
        self.u_vars = prm.u_vars
        self.p_to_q = prm.p_to_q
        self.q_to_p = prm.q_to_p
        self.p_to_u = prm.p_to_u
        self.p_leq_q = prm.p_leq_q
        self.p_leq_u = prm.p_leq_u
        self.u_leq_p = prm.u_leq_p
        self.p_eq_q = prm.p_eq_q
        self.prm = prm
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
