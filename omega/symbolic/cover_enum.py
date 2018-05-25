"""Symbolic computation of all minimal covers with orthotopes."""
# Copyright 2016-2020 by California Institute of Technology
# All rights reserved. Licensed under 3-clause BSD.
#
from __future__ import absolute_import
from __future__ import print_function
import logging

from omega.symbolic import cover as cov
from omega.symbolic.prime import support_issubset
from omega.symbolic import orthotopes as lat


log = logging.getLogger(__name__)


# This function is similar to the function `cover.minimize`.
def minimize(f, care, fol):
    """Compute minimal DNF of predicate `f` over integers.

    @param f: predicate over integer-valued variables
    @param care: care set as predicate over same variables
    @type f, care: BDD node
    @type fol: `omega.symbolic.fol.Context`

    @return: minimal covers as BDDs over parameters
    @rtype: set of BDD nodes
    """
    # reasons for permisiveness here:
    #
    # - enable inspecting env violations of assumption
    # - make errors visible
    # - use entire instantiation domain
    # - permit computing DNF for care set using same `fol.vars`
    # - tests
    if not cov._care_implies_type_hints(f, care, fol):
        log.warning('care set should imply type hints')
    # could let
    #     f &= care
    # but explicit is better.
    # Also, this permits working outside type hints.
    if not cov._f_implies_care(f, care, fol):
        log.warning('f should imply care set')
    if (f | ~ care) == fol.true:
        log.warning('f covers care set, so trivial cover')
    log.info('---- branch and bound search ----')
    prm = lat.setup_aux_vars(f, care, fol)
    lat.setup_lattice(prm, fol)
    # covering problem
    fcare = f | ~ care
    x = lat.embed_as_implicants(f, prm, fol)
    y = lat.prime_implicants(fcare, prm, fol)
    bab = cov._BranchAndBound(prm, fol)
    # initialize upper bound
    bab.upper_bound = cov._upper_bound(
        x, y, prm.p_leq_q, prm.p_to_q, fol)
    path_cost = 0.0
    mincovers = _cyclic_core_fixpoint_recursive(
        x, y, path_cost, bab, fol)
    # assert
    assert mincovers
    for cover in mincovers:
        cov.assert_is_a_cover_from_y(
            cover, y, f, prm, fol)
        low = care & ~ f
        assert cov._none_covered(cover, low, prm, fol)
    log.info('==== branch and bound search ==== ')
    return mincovers


def _print_mincovers(mincovers, fol):
    """Print count of primes and primes in each cover from `mincovers`."""
    for cover in mincovers:
        primes = list(fol.pick_iter(cover))
        print(len(primes))
        print(primes)


def _cyclic_core_fixpoint_recursive(x, y, path_cost, bab, fol):
    """Return all minimal covers of `x` made with elements from `y`."""
    log.info('\n\n---- cyclic core ----')
    assert x in fol.bdd, x
    assert y in fol.bdd, y
    assert support_issubset(x, bab.p_vars, fol)
    assert support_issubset(y, bab.p_vars, fol)
    xold, yold = x, y
    # assert `x` refines `y`
    yq = fol.let(bab.p_to_q, y)
    assert cov._cover_refines(x, yq, bab.p_leq_q, bab.p_vars, bab.q_vars, fol)
    # max ceilings and max floors
    xt = cov._max_transpose(xold, yold, bab, fol, signatures=True)
    yt = cov._max_transpose(xt, yold, bab, fol)
        # Note: This order of computation is different than
        # in the function `cover._cyclic_core_fixpoint`.
    y_floors = cov._floor(xt, yold, bab, fol, signatures=False)
    e = xt & yt  # essential elements
    x = xt & ~ e
    y = yt & ~ e
    # path_cost + cost(essential)
    new_path_cost = path_cost + cov._cost(e, bab.prm, fol)
    if (x == xold and y == yold) or (x == fol.false):
        mincovers_core = _traverse_exhaustive(x, y, new_path_cost, bab, fol)
    else:
        mincovers_core = _cyclic_core_fixpoint_recursive(
            x, y, new_path_cost, bab, fol)
    if not mincovers_core:
        return set()
    assert mincovers_core
    assert (fol.count(e) > 0) or (fol.count(y) > 0)
    # add essential elements
    r = set(mincovers_core)
    mincovers_core = set()
    for cover in r:
        assert y_floors | ~ cover == fol.true
        cover |= e
        assert fol.count(cover) > 0
        mincovers_core.add(cover)
    # enumerate all minimal covers
    assert y_floors | ~ yt == fol.true
    assert y_floors | ~ e == fol.true
    _assert_are_covers(xt, mincovers_core, bab, fol)
    _assert_covers_from(mincovers_core, yt, fol)
    _assert_uniform_cardinality(mincovers_core, fol)
    mincovers_floor = _mincovers_from_floor(
        mincovers_core, xt, y_floors, bab, fol)
    assert mincovers_floor
    _assert_are_covers(xt, mincovers_floor, bab, fol)
    _assert_covers_from(mincovers_floor, y_floors, fol)
    _assert_uniform_cardinality(mincovers_floor, fol)
    mincovers = _mincovers_from_unfloor(
        mincovers_floor, yold, bab, fol)
    assert mincovers
    _assert_are_covers(xold, mincovers, bab, fol)
    _assert_covers_from(mincovers, yold, fol)
    _assert_uniform_cardinality(mincovers, fol)
    log.info('==== cyclic core ====\n')
    return mincovers


def _mincovers_from_floor(mincovers_core, xt, y_floors, bab, fol):
    """Map minimal covers from maxima to minimal covers from floors."""
    mincovers_floor = set()
    for cover_from_max in mincovers_core:
        mincovers_below = _enumerate_mincovers_below(
            cover_from_max, xt, y_floors, bab, fol)
        assert mincovers_below
        mincovers_floor.update(mincovers_below)
    assert len(mincovers_floor) >= len(mincovers_core), (
        mincovers_floor, mincovers_core)
    return mincovers_floor


def _mincovers_from_unfloor(mincovers_floor, yold, bab, fol):
    """Minimal covers from `yold` refined by minimal covers from floors."""
    mincovers = set()
    for cover_from_floor in mincovers_floor:
        y_covers = _enumerate_mincovers_unfloor(
            cover_from_floor, yold, bab, fol)
        assert y_covers
        mincovers.update(y_covers)
    assert len(mincovers) >= len(mincovers_floor), (
        mincovers, mincovers_floor)
    return mincovers


def _assert_are_covers(x, covers, prm, fol):
    """Assert that each element of `covers` covers `x`."""
    assert support_issubset(x, prm.p_vars, fol)
    for cover in covers:
        assert support_issubset(cover, prm.p_vars, fol)
        yq = fol.let(prm.p_to_q, cover)
        assert support_issubset(yq, prm.q_vars, fol)
        assert cov._cover_refines(
            x, yq, prm.p_leq_q, prm.p_vars, prm.q_vars, fol)


def _assert_covers_from(covers, y, fol):
    """Assert that each element of `covers` is a subset of `y`."""
    for cover in covers:
        assert y | ~ cover == fol.true


def _assert_uniform_cardinality(bdds, fol):
    """Assert that each element of `bdds` has the same count of assignments."""
    if not bdds:
        return
    n = fol.count(next(iter(bdds)))
    assert n >= 0, n
    for u in bdds:
        n_ = fol.count(u)
        assert n == n_, (n, n_)


def _traverse_exhaustive(xcore, ycore, path_cost, bab, fol):
    """Compute cyclic core and terminate, prune, or recurse."""
    log.info('\n\n---- traverse ----')
    log.info('path cost: {p}'.format(p=path_cost))
    # PathLowerBound =
    #     + PathCost
    #     + Cardinality(essential)
    #     + LowerBound(core)
    core_lb = cov._lower_bound(
        xcore, ycore, bab.p_leq_q, bab.p_to_q, fol)
    branch_lb = path_cost + core_lb
    # set global lower bound only once at the top
    # because farther below in the search tree the
    # lower bounds are local, not global
    if bab.lower_bound is None:
        log.info(
            'global lower bound: {lb}'.format(lb=branch_lb))
        bab.lower_bound = branch_lb
    if xcore == fol.false:
        assert ycore == fol.false
        assert core_lb == 0, core_lb
        bab.upper_bound = branch_lb
        log.info('terminal case (empty cyclic core)\n'
                 '==== traverse ====\n')
        return {ycore}
    # A difference with the function `cover._traverse` is
    # that `>=` is replaced by `>`, to enumerate all minimal covers.
    # PathLowerBound > global_upper_bound ?
    if branch_lb > bab.upper_bound:
        log.info('prune\n'
                 '==== traverse ====\n')
        return set()
    assert xcore != fol.false
    assert ycore != fol.false
    mincovers = _branch_exhaustive(xcore, ycore, path_cost, bab, fol)
    log.info('==== traverse ====\n')
    return mincovers


def _branch_exhaustive(x, y, path_cost, bab, fol):
    log.info('\n\n---- branch ----')
    mincovers = set()
    assert support_issubset(x, bab.p_vars, fol)
    assert support_issubset(y, bab.p_vars, fol)
    d = fol.pick(y)
    assert set(d) == bab.p_vars, (d, bab.p_vars, fol.support(y))
        # must be specific implicant
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
    mincovers_left = _cyclic_core_fixpoint_recursive(
        x_minus_y, ynew, path_cost + 1, bab, fol)
    # add `y_branch` to `mincovers_left`
    r = set(mincovers_left)
    mincovers_left = set()
    for mincover in r:
        mincover |= y_branch
        mincovers_left.add(mincover)
    log.info('right branch')
    mincovers_right = _cyclic_core_fixpoint_recursive(
        x, ynew, path_cost, bab, fol)
    if not mincovers_left:
        return mincovers_right
    if not mincovers_right:
        return mincovers_left
    # pick smaller covers, or
    # take union if of same cardinality
    assert mincovers_left, mincovers_left
    assert mincovers_right, mincovers_right
    e_left = next(iter(mincovers_left))
    e_right = next(iter(mincovers_right))
    cost_left = cov._cost(e_left, bab.prm, fol)
    cost_right = cov._cost(e_right, bab.prm, fol)
    if cost_left < cost_right:
        mincovers = mincovers_left
    elif cost_left > cost_right:
        mincovers = mincovers_right
    elif cost_left == cost_right:
        mincovers = mincovers_left
        mincovers.update(mincovers_right)
    log.info('==== branch ====\n')
    return mincovers


def _enumerate_mincovers_unfloor(
        cover_from_floors, y, prm, fol):
    """Return covers from `y` that refine `cover_from_floors`.

    Relevant theorems are `MinCoverPreservedIfFloors` and
    `FloorPreservesMinCover` in `spec/MinCover.tla`.

    Any minimal cover from `y` is enumerated because it is refined by some
    minimal cover from `Floors(y, x)`.
    All enumerated sets are covers and minimal, because of their cardinality.

    @rtype: `set` of BDD nodes
    """
    lm = list(_pick_iter_as_bdd(cover_from_floors, fol))
    n = len(lm)
    assert n >= 1, n
    mincovers_above = set()
    partials = {fol.false}
    while partials:
        partial_cover = partials.pop()
        i = fol.count(partial_cover)
        assert i <= n, (i, n)
        if i == n:
            mincovers_above.add(partial_cover)
            continue
        assert i < n, (i, n)
        k = i + 1
        yfloor = lm[k - 1]
        succ = _y_unfloor(yfloor, y, prm, fol)
        for z in _pick_iter_as_bdd(succ, fol):
            assert z != fol.false
            new_cover = partial_cover | z
            k_ = fol.count(new_cover)
            # This assertion ensures that cardinality of
            # the cover is preserved (injective mapping).
            assert k == k_, (k, k_)
            partials.add(new_cover)
    assert mincovers_above
    return mincovers_above


def _y_unfloor(yfloor, y, prm, fol):
    """Compute the elements from `y` that are above `yfloor`."""
    assert support_issubset(yfloor, prm.p_vars, fol)
    d = fol.pick(yfloor)
    assert set(d) == prm.p_vars, d
    yq = fol.let(prm.p_to_q, y)  # y(q)
    p_leq_y = prm.p_leq_q & yq  # Leq[z(p), y(q)]
    y_over_q = fol.let(d, p_leq_y)  # ThoseOver(y, yfloor)(q)
    y_over = fol.let(prm.q_to_p, y_over_q)  # ThoseOver(y, yfloor)(p)
    assert support_issubset(y_over, prm.p_vars, fol)
    assert y_over != fol.false
    return y_over


def _enumerate_mincovers_below_set_based(
        cover_from_max, x, y, prm, fol):
    """Return covers from `y` that refine `cover_from_max`.

    @rtype: `set` of BDD nodes
    """
    # cover_from_max => y
    assert y | ~ cover_from_max == fol.true
    lm = list(_pick_iter_as_bdd(cover_from_max, fol))
    n = len(lm)
    assert n >= 1, n
    mincovers_below = set()
    partials = {fol.false}
    while partials:
        partial_cover = partials.pop()
        i = fol.count(partial_cover)
        assert i <= n, (i, n)
        if i == n:
            mincovers_below.add(partial_cover)
            continue
        assert i < n, (i, n)
        k = i + 1
        assert k >= 0, k
        ymax = lm[k - 1]
        assert y | ~ ymax == fol.true
        cover = partial_cover | _lm_tail(k, lm)
        n_ = fol.count(cover)
        assert n == n_, (n, n_)
        succ = _below_and_suff(ymax, cover, x, y, prm, fol)
        for z in _pick_iter_as_bdd(succ, fol):
            assert z != fol.false
            new_cover = partial_cover | z
            k_ = fol.count(new_cover)
            assert k == k_, (k, k_)
            partials.add(new_cover)
    assert mincovers_below
    return mincovers_below


# This variant of the function
# `_enumerate_mincovers_below_set_based`
# uses a stack.
def _enumerate_mincovers_below(
        cover_from_max, x, y, prm, fol):
    """Return covers from `y` that refine `cover_from_max`.

    @rtype: `set` of BDD nodes
    """
    # cover_from_max => y
    assert y | ~ cover_from_max == fol.true
    # arrange cover in a fixed order
    lm = list(_pick_iter_as_bdd(cover_from_max, fol))
    n = len(lm)
    assert n >= 1, n
    mincovers_below = set()
    stack = [fol.false]
    while stack:
        partial_cover = stack.pop()
        i = fol.count(partial_cover)
        assert i <= n, (i, n)
        # action `Collect`
        if i == n:
            mincovers_below.add(partial_cover)
            continue
        # action `Expand`
        assert i < n, (i, n)
        k = i + 1
        assert k >= 0, k
        ymax = lm[k - 1]
        assert y | ~ ymax == fol.true
        patch = _lm_tail(k, lm)
        cover = partial_cover | patch
        assert fol.count(cover) == n, fol.count(cover)
        succ = _below_and_suff(
            ymax, cover, x, y, prm, fol)
        for z in _pick_iter_as_bdd(succ, fol):
            assert z != fol.false
            new_cover = partial_cover | z
            assert fol.count(new_cover) == k, fol.count(new_cover)
            stack.append(new_cover)
    assert mincovers_below
    return mincovers_below


def _pick_iter_as_bdd(u, fol):
    """Return generator of BDDs from `pick_iter(u)`.

    @param u: BDD node
    @param fol: `fol.Context`
    @rtype: generator of BDD nodes
    """
    for d in fol.pick_iter(u):
        yield fol.assign_from(d)


def _below_and_suff(ymax, cover, x, y, prm, fol):
    """Return subset of `y` that is below `ymax` and suffices.

    A `yk \in y` suffices if it covers all elements in `x`
    that are covered by `ymax` but not by any element of `y`
    other than `ymax`.
    """
    assert support_issubset(ymax, prm.p_vars, fol)
    assert support_issubset(cover, prm.p_vars, fol)
    assert support_issubset(x, prm.p_vars, fol)
    assert support_issubset(y, prm.p_vars, fol)
    assert ymax != fol.false
    assert (cover | ~ ymax) == fol.true
    # `cover` is Q
    other_y = cover & ~ ymax
    p_leq_q = prm.p_leq_q
    other_yq = fol.let(prm.p_to_q, other_y)
    u = x & p_leq_q & other_yq
    u = fol.exist(prm.q_vars, u)
    # x covered by only `ymax`, among those y in` cover`
    x_sig_ymax = x & ~ u  # Only(ymax, cover)
    assert x_sig_ymax != fol.false
    # find the y above these x,
    # and below ymax
    assert (y | ~ ymax) == fol.true
    yq = fol.let(prm.p_to_q, y)
    ymax_q = fol.let(prm.p_to_q, ymax)
    u = (p_leq_q & yq) | ~ x_sig_ymax
    u = fol.forall(prm.p_vars, u)
    assert u != fol.false
    # Yonly == {y \in Y:  \A q \in Only(ymax, cover):  Leq[q, y]}
    y_only = fol.let(prm.q_to_p, u)
    u = y_only & p_leq_q & ymax_q
    # {y \in Yonly:  Leq[y, ymax]}
    yk_set = fol.exist(prm.q_vars, u)
    assert support_issubset(yk_set, prm.p_vars, fol)
    assert yk_set != fol.false
    return yk_set


def _lm_tail(k, lm):
    """Return elements of `Lm` with indices `k..N`."""
    n = len(lm)
    assert k >= 1, k
    assert k <= n, (k, n)
    start = k - 1
    assert start >= 0, start
    r = lm[start]
    for i in range(start, n):
        r |= lm[i]
    return r


def to_expr(fol, u, care=None, **kw):
    """Return all minimal DNFs of integer inequalities.

    For now, this method requires that all variables in
    `support(u)` be integers.

    @param care: BDD of care set
    @param kw: keyword args are passed to
        function `cover.dumps_cover`.
    """
    if care is None:
        care = fol.bdd.true
    mincovers = minimize(u, care, fol)
    dnfs = list()
    for cover in mincovers:
        s = cov.dumps_cover(
            cover, u, care, fol, **kw)
        dnfs.append(s)
    return dnfs
