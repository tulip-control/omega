"""Test `omega.symbolic.cover_enum`."""
import itertools
import pprint

from nose.tools import assert_raises
from omega.symbolic import cover as cov
from omega.symbolic import cover_enum as cov_enum
from omega.symbolic import fol as _fol
from omega.symbolic import orthotopes as lat


def test_cyclic_core_with_care_set():
    fol = _fol.Context()
    fol.declare(x=(0, 17))
    s = '(x < 15)'
    f = fol.add_expr(s)
    care_set = fol.true
    mincovers = cov_enum.minimize(f, care_set, fol)
    mincovers_ = {fol.add_expr('a_x = 0 /\ b_x = 14')}
    assert mincovers == mincovers_, list(
        fol.pick_iter(mincovers))


def test_example_of_strong_reduction():
    """Computing all minimal covers for the counterexample."""
    # For now `cov.minimize` creates the primes etc in
    # a specific way, for a specific basis (orthotopes).
    # This example doesn't fit in that recipe,
    # so we rewrite some of the code in `minimize`.
    fol = _fol.Context()
    fol.to_bdd = fol.add_expr
    x_vars = dict(x=(0, 8))
    p_vars = dict(p=(0, 8))
    q_vars = dict(q=(0, 8))
    u_vars = dict(p_cp=(0, 8))
    fol.declare(**x_vars)
    fol.declare(**p_vars)
    fol.declare(**q_vars)
    fol.declare(**u_vars)
    p_eq_q = fol.to_bdd(r'p \in 0..8  /\  q \in 0..8  /\ p = q')
    leq = r'''
    # (* layer 1 *)
    \/ (p = 0  /\  q = 6)
    \/ (p = 0  /\  q = 7)
    \/ (p = 0  /\  q = 8)
    # (* layer 2 *)
    \/ (p = 6  /\  q = 2)
    \/ (p = 6  /\  q = 3)
    \/ (p = 7  /\  q = 3)
    \/ (p = 7  /\  q = 4)
    \/ (p = 8  /\  q = 4)
    \/ (p = 8  /\  q = 5)
    # (* layer 3 *)
    \/ (p = 2  /\  q = 1)
    \/ (p = 3  /\  q = 1)
    \/ (p = 4  /\  q = 1)
    \/ (p = 5  /\  q = 1)
    # transitivity
    \/ (p = 0 /\ q = 2)
    \/ (p = 0 /\ q = 3)
    \/ (p = 0 /\ q = 4)
    \/ (p = 0 /\ q = 5)
    \/ (p = 0 /\ q = 1)

    \/ (p = 6 /\ q = 1)
    \/ (p = 7 /\ q = 1)
    \/ (p = 8 /\ q = 1)
    # equality
    \/ (p = q /\ p \in 0..8 /\ q \in 0..8)
    '''
    p_leq_q = fol.to_bdd(leq)
    u_leq_p = fol.to_bdd(leq.replace('p', 'p_cp').replace('q', 'p'))
    p_leq_u = fol.to_bdd(leq.replace('q', 'p_cp'))
    # bundle
    prm = Parameters()
    prm.x_vars = set(x_vars)
    prm.p_vars = set(p_vars)
    prm.q_vars = set(q_vars)
    prm.u_vars = set(u_vars)
    #
    prm.p_to_q = dict(p='q')
    prm.q_to_p = dict(q='p')
    prm.p_to_u = dict(p='p_cp')
    #
    prm.u_leq_p = u_leq_p
    prm.p_leq_u = p_leq_u
    prm.p_leq_q = p_leq_q
    prm.p_eq_q = p_eq_q
    #
    x = fol.add_expr(r'p \in 6..8')
    y = fol.add_expr(r'p \in 2..5')
    #
    path_cost = 0.0
    bab = cov._BranchAndBound(prm, fol)
    bab.upper_bound = cov._upper_bound(
        x, y, prm.p_leq_q, prm.p_to_q, fol)
    path_cost = 0.0
    mincovers = cov_enum._cyclic_core_fixpoint_recursive(
        x, y, path_cost, bab, fol)
    # enumerative check
    enumerated_covers(x, y, prm, fol)
    print('all minimal covers:')
    cov_enum._print_mincovers(mincovers, fol)
    # assert set of minimal covers is as expected
    assert len(mincovers) == 3, mincovers
    mincovers_t = set()
    for cover in mincovers:
        c = set()
        for d in fol.pick_iter(cover):
            r, = d.values()
            c.add(r)
        c = tuple(sorted(c))
        mincovers_t.add(c)
    mincovers_t_ = {(2, 4), (3, 4), (3, 5)}
    assert mincovers_t == mincovers_t_, (mincovers_t, mincovers_t_)


def enumerated_covers(x, y, prm, fol):
    """Return all minimal covers by enumerative search."""
    xelem = list(fol.pick_iter(x))
    yelem = list(fol.pick_iter(y))
    all_subsets = subsets(yelem)
    covers = list()
    for subset in all_subsets:
        if subset_is_cover(xelem, subset, prm.p_leq_q, prm.p_to_q, fol):
            covers.append(subset)
    assert covers
    n = len(next(iter(covers)))
    for subset in covers:
        n = min(n, len(subset))
    mincovers = [c for c in covers if len(c) == n]
    pprint.pprint(mincovers)
    return mincovers


def subset_is_cover(x, subset, p_leq_q, p_to_q, fol):
    """Return `True` if `subset` covers `x` using `p_leq_q`."""
    for u in x:
        if not element_is_covered(u, subset, p_leq_q, p_to_q, fol):
            return False
    return True


def element_is_covered(u, subset, p_leq_q, p_to_q, fol):
    """Return `True` if some element of `subset` covers `u`.

    Covering is computed using `p_leq_q`.
    """
    r = fol.let(u, p_leq_q)
    for y in subset:
        yq = {p_to_q[k]: v for k, v in y.items()}
        if fol.let(yq, r) == fol.true:
            return True
    return False


def subsets(c):
    """Return a `set` with all subsets of `c`, as tuples."""
    sets = list()
    for i in range(len(c) + 1):
        t = itertools.combinations(c, i)
        sets.extend(t)
    return sets


class Parameters(object):
    """Stores parameter values and lattice definition."""

    def __init__(self):
        x_vars = list()
        # variable type hints (as `set`)
        self.x_vars = None
        self.p_vars = None
        self.q_vars = None
        self.u_vars = None
        # mappings between variables
        self.p_to_q = None
        self.q_to_p = None
        self.p_to_u = None
        # relations
        self.u_leq_p = None
        self.p_leq_u = None
        self.p_leq_q = None
        self.p_eq_q = None
        self.fol = None


def test_cyclic_core_recursion():
    """One cyclic core."""
    fol = _fol.Context()
    fol.declare(
        x=(0, 1), y=(0, 1), z=(0, 1))
    s = r'''
        (
            \/ (z = 1  /\  y = 0)
            \/ (x = 0  /\  z = 1)
            \/ (y = 1  /\  x = 0)
            \/ (y = 1  /\  z = 0)
            \/ (x = 1  /\  z = 0)
            \/ (x = 1  /\  y = 0)
        )
        '''
    f = fol.add_expr(s)
    care = fol.true
    # setup variables and lattice
    prm = lat.setup_aux_vars(f, care, fol)
    lat.setup_lattice(prm, fol)
    # covering problem
    fcare = f | ~ care
    x = lat.embed_as_implicants(f, prm, fol)
    y = lat.prime_implicants(fcare, prm, fol)
    # enumerative check
    enumerated_covers(x, y, prm, fol)
    # symbolically minimize
    mincovers = cov_enum.minimize(f, care, fol)
    n = len(mincovers)
    assert n == 2, (n, mincovers)
    for cover in mincovers:
        n = fol.count(cover)
        primes = list(fol.pick_iter(cover))
        assert n == 3, (n, primes)


def test_cyclic_core_recursion_1():
    """One cyclic core."""
    fol = _fol.Context()
    fol.declare(
        x=(0, 1), y=(0, 1), z=(0, 1))
    s = r'''
        (
            \/ (z = 1  /\  y = 0)
            \/ (x = 0  /\  z = 1)
            \/ (y = 1  /\  x = 0)
            \/ (y = 1  /\  z = 0)
            \/ (x = 1  /\  z = 0)
            \/ (x = 1  /\  y = 0)
        )
        '''
    f = fol.add_expr(s)
    care_set = fol.true
    mincovers = cov_enum.minimize(f, care_set, fol)
    n = len(mincovers)
    assert n == 2, (n, mincovers)
    for cover in mincovers:
        n = fol.count(cover)
        primes = list(fol.pick_iter(cover))
        assert n == 3, (n, primes)


def test_cyclic_core_recursion_2():
    """Two cyclic cores, in orthogonal subspaces."""
    fol = _fol.Context()
    fol.declare(
        x=(0, 1), y=(0, 1), z=(0, 1),
        u=(0, 1), v=(0, 1), w=(0, 1))
    s = r'''
        (
            \/ (z = 1  /\  y = 0)
            \/ (x = 0  /\  z = 1)
            \/ (y = 1  /\  x = 0)
            \/ (y = 1  /\  z = 0)
            \/ (x = 1  /\  z = 0)
            \/ (x = 1  /\  y = 0)
        ) \/
        (
            \/ (w = 1  /\  v = 0)
            \/ (u = 0  /\  w = 1)
            \/ (v = 1  /\  u = 0)
            \/ (v = 1  /\  w = 0)
            \/ (u = 1  /\  w = 0)
            \/ (u = 1  /\  v = 0)
        )
        '''
    f = fol.add_expr(s)
    care_set = fol.true
    mincovers = cov_enum.minimize(f, care_set, fol)
    n = len(mincovers)
    assert n == 4, (n, mincovers)
    for cover in mincovers:
        n = fol.count(cover)
        primes = list(fol.pick_iter(cover))
        assert n == 6, (n, primes)


def test_cyclic_core_recursion_3():
    """Three cyclic cores, in orthogonal subspaces."""
    fol = _fol.Context()
    fol.declare(
        x=(0, 1), y=(0, 1), z=(0, 1),
        u=(0, 1), v=(0, 1), w=(0, 1),
        a=(0, 1), b=(0, 1), c=(0, 1))
    s = r'''
        (
            \/ (z = 1  /\  y = 0)
            \/ (x = 0  /\  z = 1)
            \/ (y = 1  /\  x = 0)
            \/ (y = 1  /\  z = 0)
            \/ (x = 1  /\  z = 0)
            \/ (x = 1  /\  y = 0)
        ) \/
        (
            \/ (w = 1  /\  v = 0)
            \/ (u = 0  /\  w = 1)
            \/ (v = 1  /\  u = 0)
            \/ (v = 1  /\  w = 0)
            \/ (u = 1  /\  w = 0)
            \/ (u = 1  /\  v = 0)
        ) \/
        (
            \/ (c = 1  /\  b = 0)
            \/ (a = 0  /\  c = 1)
            \/ (b = 1  /\  a = 0)
            \/ (b = 1  /\  c = 0)
            \/ (a = 1  /\  c = 0)
            \/ (a = 1  /\  b = 0)
        )
        '''
    f = fol.add_expr(s)
    care_set = fol.true
    mincovers = cov_enum.minimize(f, care_set, fol)
    n = len(mincovers)
    assert n == 8, (n, mincovers)
    for cover in mincovers:
        n = fol.count(cover)
        primes = list(fol.pick_iter(cover))
        assert n == 9, (n, primes)


def test_cyclic_core_fixpoint_recursive():
    fol = _fol.Context()
    p_vars = dict(p=(0, 3))
    q_vars = dict(q=(0, 3))
    u_vars = dict(p_cp=(0, 3))
    fol.declare(**p_vars)
    fol.declare(**q_vars)
    fol.declare(**u_vars)
    p_eq_q = fol.to_bdd(r'p \in 0..3 /\ p = q')
    # 3
    # | |
    # 1 2
    # | |
    # 0
    leq = r'''
    # (* layer 1 *)
    \/ (p = 0  /\  q = 1)
    \/ (p = 0  /\  q = 2)
    # (* layer 2 *)
    \/ (p = 1  /\  q = 3)
    \/ (p = 2  /\  q = 3)
    # transitivity
    \/ (p = 0 /\ q = 3)
    # equality
    \/ (p = q /\ p \in 0..3)
    '''
    p_leq_q = fol.to_bdd(leq)
    u_leq_p = fol.to_bdd(leq.replace('p', 'p_cp').replace('q', 'p'))
    p_leq_u = fol.to_bdd(leq.replace('q', 'p_cp'))
    # bundle
    prm = Parameters()
    prm.p_vars = set(p_vars)
    prm.q_vars = set(q_vars)
    prm.u_vars = set(u_vars)
    #
    prm.p_to_q = dict(p='q')
    prm.q_to_p = dict(q='p')
    prm.p_to_u = dict(p='p_cp')
    #
    prm.u_leq_p = u_leq_p
    prm.p_leq_u = p_leq_u
    prm.p_leq_q = p_leq_q
    prm.p_eq_q = p_eq_q
    #
    x = fol.add_expr('p = 0')
    y = fol.add_expr(r'p \in 1..2')
    #
    path_cost = 0.0
    bab = cov._BranchAndBound(prm, fol)
    bab.upper_bound = cov._upper_bound(
        x, y, prm.p_leq_q, prm.p_to_q, fol)
    path_cost = 0.0
    mincovers = cov_enum._cyclic_core_fixpoint_recursive(
        x, y, path_cost, bab, fol)
    assert len(mincovers) == 2, mincovers
    mincovers_ = {
        fol.add_expr('p = 1'),
        fol.add_expr('p = 2')}
    assert mincovers == mincovers_, list(
        fol.pick_iter(mincovers))


def test_assert_are_covers():
    fol = _fol.Context()
    fol.declare(p=(0, 4), q=(0, 4))
    x = fol.add_expr('p = 1')
    covers = {
        fol.add_expr('p = 1'),
        fol.add_expr('p = 2'),
        fol.add_expr(r'p \in 3..4')}
    prm = Parameters()
    prm.p_vars = {'p'}
    prm.q_vars = {'q'}
    prm.p_to_q = {'p': 'q'}
    prm.p_leq_q = fol.add_expr('p <= q')
    cov_enum._assert_are_covers(x, covers, prm, fol)
    # not covers
    x = fol.add_expr('p = 2')
    with assert_raises(AssertionError):
        cov_enum._assert_are_covers(x, covers, prm, fol)


def test_assert_covers_from():
    fol = _fol.Context()
    fol.declare(p=(0, 4))
    y = fol.add_expr(r'p \in 1..3')
    covers = {
        fol.add_expr('p = 1'),
        fol.add_expr(r'p \in 1..2'),
        fol.add_expr(r'p \in 2..3')}
    cov_enum._assert_covers_from(covers, y, fol)
    # not covers from `y`
    y = fol.add_expr('p = 4')
    with assert_raises(AssertionError):
        cov_enum._assert_covers_from(covers, y, fol)


def test_assert_uniform_cardinality():
    fol = _fol.Context()
    fol.declare(p=(0, 3))
    bdds = {
        fol.add_expr(r'p \in 0..1'),
        fol.add_expr(r'p \in 2..3'),
        fol.add_expr(r'p = 0 \/ p = 3')}
    cov_enum._assert_uniform_cardinality(bdds, fol)
    # not of uniform cardinality
    bdds = {
        fol.add_expr('p = 0'),
        fol.add_expr(r'p \in 2..3')}
    with assert_raises(AssertionError):
        cov_enum._assert_uniform_cardinality(bdds, fol)


def test_enumerate_mincovers_unfloor():
    fol = _fol.Context()
    fol.declare(p=(0, 4), q=(0, 4))
    # define a fragment of a lattice
    prm = Parameters()
    prm.p_vars = {'p'}
    prm.p_to_q = {'p': 'q'}
    prm.q_to_p = {'q': 'p'}
    # 2 3
    # | |
    # 0 1
    prm.p_leq_q = fol.add_expr(r'''
        \/ (p = 0 /\ q = 2)
        \/ (p = 1 /\ q = 3)
        ''')
    # {0..1} |-> {2..3}
    y = fol.add_expr(r'p \in 2..3')
    cover_from_floors = fol.add_expr(r'p \in 0..1')
    mincovers = cov_enum._enumerate_mincovers_unfloor(
        cover_from_floors, y, prm, fol)
    assert len(mincovers) == 1, mincovers
    assert y in mincovers, (mincovers, y)
    # non-injective case
    # 2 2 3
    # | | |
    # 0 1 1
    prm.p_leq_q = fol.add_expr(r'''
        \/ (p = 0 /\ q = 2)
        \/ (p = 1 /\ q = 2)
        \/ (p = 1 /\ q = 3)
        ''')
    y = fol.add_expr(r'p \in 2..3')
    cover_from_floors = fol.add_expr(r'p \in 0..1')
    with assert_raises(AssertionError):
        # The assertion error is raised because the cover's cardinality
        # is reduced by the mapping, so the cardinality of the
        # partial cover is smaller than expected (`assert k == k_` within
        # the function `_enumerate_mincovers_unfloor`).
        mincovers = cov_enum._enumerate_mincovers_unfloor(
            cover_from_floors, y, prm, fol)
    # {0..1} |-> {2..3, {2, 4}}
    prm.p_leq_q = fol.add_expr(r'''
        \/ (p = 0 /\ q = 2)
        \/ (p = 1 /\ q = 3)
        \/ (p = 1 /\ q = 4)
        ''')
    y = fol.add_expr(r'p \in 2..4')
    cover_from_floors = fol.add_expr(r'p \in 0..1')
    mincovers = cov_enum._enumerate_mincovers_unfloor(
        cover_from_floors, y, prm, fol)
    assert len(mincovers) == 2, mincovers
    cover = fol.add_expr(r'p \in 2..3')
    assert cover in mincovers, (mincovers, cover)
    cover = fol.add_expr(r'p = 2 \/ p = 4')
    assert cover in mincovers, (mincovers, cover)


def test_y_unfloor():
    fol = _fol.Context()
    fol.declare(p=(0, 3), q=(0, 3))
    # define a fragment of a lattice
    prm = Parameters()
    prm.p_vars = {'p'}
    prm.p_to_q = {'p': 'q'}
    prm.q_to_p = {'q': 'p'}
    # 2 3
    # | |
    # 0 1
    prm.p_leq_q = fol.add_expr(r'''
        \/ (p = 0 /\ q = 2)
        \/ (p = 1 /\ q = 3)
        ''')
    y = fol.add_expr(r'p \in 2..3')
    # yfloor = 0
    yfloor = fol.add_expr('p = 0')
    y_over = cov_enum._y_unfloor(yfloor, y, prm, fol)
    y_over_ = fol.add_expr('p = 2')
    assert y_over == y_over_, list(fol.pick_iter(y_over))
    # yfloor = 1
    yfloor = fol.add_expr('p = 1')
    y_over = cov_enum._y_unfloor(yfloor, y, prm, fol)
    y_over_ = fol.add_expr('p = 3')
    assert y_over == y_over_, list(fol.pick_iter(y_over))


def test_enumerate_mincovers_below():
    """Test the function `enumerate_mincovers_below`."""
    fol = _fol.Context()
    fol.declare(x=(0, 5))
    u = fol.add_expr(r' x \in 0..1 ')
    care = fol.true
    prm = lat.setup_aux_vars(u, care, fol)
    lat.setup_lattice(prm, fol)
    x = fol.add_expr(r' a_x = 0 /\ b_x = 2 ')
    y = fol.add_expr(r'''
        \/ (a_x = 0 /\ b_x = 1)
        \/ (a_x = 0 /\ b_x = 3)
        \/ (a_x = 0 /\ b_x = 4)
        ''')
    cover_from_max = fol.add_expr(r'''
        a_x = 0 /\ b_x = 4
        ''')
    mincovers_below = cov_enum._enumerate_mincovers_below(
        cover_from_max, x, y, prm, fol)
    mincovers_below_ = cov_enum._enumerate_mincovers_below_set_based(
        cover_from_max, x, y, prm, fol)
    assert mincovers_below == mincovers_below_, mincovers_below
    r = fol.add_expr(r'''
        \/ (a_x = 0 /\ b_x = 3)
        \/ (a_x = 0 /\ b_x = 4)
        ''')
    mincovers_below_ = set(
        fol.assign_from(d) for d in fol.pick_iter(r))
    assert mincovers_below == mincovers_below_, (
        mincovers_below, mincovers_below_)


def test_pick_iter_as_bdd():
    fol = _fol.Context()
    fol.declare(x=(0, 5))
    u = fol.add_expr(r' x \in 0..1 ')
    t = list(cov_enum._pick_iter_as_bdd(u, fol))
    t_ = [fol.add_expr('x = 0'),
          fol.add_expr('x = 1')]
    assert t == t_, (t, t_)


def test_below_and_suff():
    fol = _fol.Context()
    fol.declare(p=(0, 3), q=(0, 3))
    # define a fragment of a lattice
    prm = Parameters()
    prm.p_vars = {'p'}
    prm.q_vars = {'q'}
    prm.p_to_q = {'p': 'q'}
    prm.q_to_p = {'q': 'p'}
    # 3
    # | |
    # 1 2
    # |
    # 0
    prm.p_leq_q = fol.add_expr(r'''
        \/ (p = 0 /\ q = 1)
        \/ (p = 0 /\ q = 3)
        \/ (p = 1 /\ q = 3)
        \/ (p = 2 /\ q = 3)
        \/ (p \in 0..3 /\ p = q)
        ''')
    ymax = fol.add_expr('p = 3')
    cover = fol.add_expr('p = 3')
    x = fol.add_expr('p = 0')
    y = fol.add_expr(r'p \in 1..3')
    yk_set = cov_enum._below_and_suff(
        ymax, cover, x, y, prm, fol)
    yk_set_ = fol.add_expr(r'p = 1 \/ p = 3')
    assert yk_set == yk_set_, list(
        fol.pick_iter(yk_set))


def test_lm_tail():
    fol = _fol.Context()
    fol.declare(x=(0, 5))
    # N = 3
    lm = [fol.add_expr('x = 0'),  # index 1
          fol.add_expr('x = 1'),  # index 2
          fol.add_expr('x = 2')]  # index 3
    k = 0
    with assert_raises(AssertionError):
        cov_enum._lm_tail(k, lm)
    k = 1
    r = cov_enum._lm_tail(k, lm)
    r_ = fol.add_expr(r'x \in 0..2')
    assert r == r_, list(fol.pick_iter(r))
    k = 2
    r = cov_enum._lm_tail(k, lm)
    r_ = fol.add_expr(r'x \in 1..2')
    assert r == r_, list(fol.pick_iter(r))
    k = 3
    r = cov_enum._lm_tail(k, lm)
    r_ = fol.add_expr('x = 2')
    assert r == r_, list(fol.pick_iter(r))
    k = 4
    with assert_raises(AssertionError):
        cov_enum._lm_tail(k, lm)


def test_to_expr():
    fol = _fol.Context()
    fol.declare(x=(0, 1), y=(0, 1), z=(0, 1))
    s = r'''
            \/ (z = 1  /\  y = 0)
            \/ (x = 0  /\  z = 1)
            \/ (y = 1  /\  x = 0)
            \/ (y = 1  /\  z = 0)
            \/ (x = 1  /\  z = 0)
            \/ (x = 1  /\  y = 0)
        '''
    u = fol.add_expr(s)
    care = fol.true
    dnfs = cov_enum.to_expr(fol, u, care=care, show_dom=True)
    assert len(dnfs) == 2, dnfs
    for dnf in dnfs:
        print(dnf)


if __name__ == '__main__':
    test_example_of_strong_reduction()
