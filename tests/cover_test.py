"""Test `omega.symbolic.cover`."""
from itertools import cycle
import logging
import pprint
import time

# import matplotlib as mpl
# mpl.use('Agg')
# from matplotlib import pyplot as plt
plt = None  # uncomment if you want to plot
import omega.logic.syntax as stx
from omega.symbolic.prime import support_issubset
import omega.symbolic.fol as _fol
import omega.symbolic.cover as cov
import omega.symbolic.orthotopes as lat
import omega.symbolic._type_hints as tyh
import pytest


log = logging.getLogger(__name__)
logger = logging.getLogger('dd')
logger.setLevel(logging.ERROR)
logger = logging.getLogger('omega')
logger.setLevel(logging.ERROR)


def test_scaling_equality():
    aut = _fol.Context()
    x_vars = dict(x=(0, 10), y=(0, 15), z=(0, 15))
    aut.declare(**x_vars)
    params = dict(pa='a', pb='b', qa='u', qb='v')
    p_dom = lat._parameter_table(
        x_vars, aut.vars,
        a_name=params['pa'], b_name=params['pb'])
    q_dom = lat._parameter_table(
        x_vars, aut.vars,
        a_name=params['qa'], b_name=params['qb'])
    aut.declare(**p_dom)
    aut.declare(**q_dom)
    px = lat._map_vars_to_parameters(
        x_vars, a_name=params['pa'], b_name=params['pb'])
    qx = lat._map_vars_to_parameters(
        x_vars, a_name=params['qa'], b_name=params['qb'])
    p_to_q = lat._renaming_between_parameters(px, qx)
    x_as_x = {xj: dict(a=xj, b=xj) for xj in px}
    varmap = lat.parameter_varmap(px, x_as_x)
    log.info(f'Number of variables: {len(varmap)}')
    u = lat.subseteq(varmap, aut)
    #
    s = (
        r'( '
        r'(z = 1  /\  y <= 0)  \/ '
        r'(x = 0  /\  z = 1)  \/ '
        r'(y >= 1  /\  x <= 0)  \/ '
        r'(y >= 1  /\  z <= 0)  \/ '
        r'(x >= 1  /\  z <= 0)  \/ '
        r'(x >= 1  /\  y <= 0) '
        r') ')
    f = aut.add_expr(s)
    prm = lat.Parameters()
    prm._px = px
    lat.embed_as_implicants(f, prm, aut)


def test_using_fol_context():
    c = _fol.Context()
    c.declare(x=(0, 5), y=(-4, 6))
    s = (r'1 <= x /\ x <= 3 /\ -2 <= y /\ y <= 4')
    u = c.add_expr(s)
    care = c.true
    r = cov.minimize(u, care, c)
    s = cov.dumps_cover(r, u, care, c, show_limits=True)
    assert r'x \in 1 .. 3' in s, s
    assert r'y \in -2 .. 4' in s, s
    s_ = '''\
(* `f` depends on:  x, y *)
(* `care` depends on:   *)
(* The minimal cover is: *)
/\\ x \\in 0 .. 7
/\\ y \\in -8 .. 7
/\\ (x \\in 1 .. 3) /\\ (y \\in -2 .. 4)'''
    assert s == s_, (s, s_)


# TODO: try this with incrementally larger care sets
def test_branching():
    aut = _fol.Context()
    aut.bdd.configure(reordering=True)
    # aut.bdd = _bdd.BDD(memory_estimate=2 * _bdd.GB)
    # aut.bdd.configure(
    #     max_memory=2 * _bdd.GB,
    #     max_cache_hard=2**25)
    aut.declare(x=(0, 10), y=(0, 25), z=(0, 25))
    s = (
        r'( '
        r'(z = 1  /\  y <= 0)  \/ '
        r'(x = 0  /\  z = 1)  \/ '
        r'(y >= 1  /\  x <= 0)  \/ '
        r'(y >= 1  /\  z <= 0)  \/ '
        r'(x >= 1  /\  z <= 0)  \/ '
        r'(x >= 1  /\  y <= 0) '
        r') ')
    f = aut.add_expr(s)
    s = (
        r'0 <= x  /\  x <= 2  /\ '
        r'0 <= y  /\  y <= 1  /\ '
        r'0 <= z  /\  z <= 1 '
        )
    care_set = aut.add_expr(s)
    # care_set = aut.true
    cover = cov.minimize(f, care_set, aut)
    s = cov.dumps_cover(cover, f, care_set, aut)
    log.info(s)


def test_cost():
    r = cov._cost(None, '?', '?')
    assert r == float('inf'), r
    fol, prm = setup_aut()
    # assign here to avoid calling `eq` from `setup_aut`
    # to ensure unit testing
    prm.p_eq_q = lat.eq(prm._varmap, fol)
    s = (
        r'1 <= a_x /\ a_x <= 3 /\ b_x = 6 /\ '
        r'2 <= a_y /\ a_y <= 5 /\ '
        r'0 <= b_y /\ b_y <= 7')
    u = fol.add_expr(s)
    r = cov._cost(u, prm, fol)
    assert r == 96, r


def test_cyclic_core_using_robots_example():
    aut, _ = setup_aut(15, 15)
    f = robots_example(aut)
    care_set = aut.true
    xcore, ycore, essential = cov.cyclic_core(f, care_set, aut)
    assert xcore == aut.false, xcore
    n_essential = aut.count(essential)
    k = aut.count(essential)
    assert n_essential == k, (n_essential, k)
    assert n_essential == 7, n_essential


def test_orthotopes_using_robots_example():
    aut, prm = setup_aut(15, 15)
    p_vars = prm.p_vars
    # this predicate is constructed by `contract_maker`
    # for the robots example in ACC 2016
    f = robots_example(aut)
    prm.p_leq_q = lat.subseteq(prm._varmap, aut)
    prm.p_eq_q = lat.eq(prm._varmap, aut)
    u = lat.prime_implicants(f, prm, aut)
    support = aut.support(u)
    assert support == set(p_vars), (support, p_vars)
    n_primes = aut.count(u)
    k = aut.count(u)
    assert n_primes == k, (n_primes, k)
    log.info(f'{n_primes} prime implicants')
    u = lat.essential_orthotopes(f, prm, aut)
    support = aut.support(u)
    assert support == set(p_vars), (support, p_vars)
    n_essential = aut.count(u)
    k = aut.count(u)
    assert n_essential == k, (n_essential, k)
    log.info(f'{n_essential} essential prime implicants')
    assert n_essential == 7, n_essential
    # result: all primes are essential in this example
    #
    care = aut.true
    s = cov.dumps_cover(u, f, care, aut)
    log.info(s)
    log.info(f'BDD has {len(aut.bdd)} nodes')
    # confirm that essential orthotopes cover exactly `f`
    c = lat.list_expr(u, prm, aut, simple=True)
    s = stx.disj(c)
    log.info(s)
    z = aut.add_expr(s)
    z = aut.exist(['a_x', 'b_x', 'a_y', 'b_y'], z)
    assert aut.support(z) == aut.support(f)
    assert z == f
    if plt is not None:
        _plot_orthotopes_for_robots_example(u, f, prm._px, xvars, aut)
    # pprint.pprint(aut.bdd.statistics())
    # pprint.pprint(aut.bdd.vars)
    log.info(f'{len(aut.bdd)} nodes in manager')


def _plot_orthotopes_for_robots_example(u, f, abx, xvars, aut):
    kw = dict(color='black', marker='o', linestyle='none')
    ax = plt.axes()
    ax.set_xlim([0, 10])
    ax.set_ylim([0, 10])
    cov.plot_orthotopes(u, abx, xvars, aut, ax)
    cov.plot_points(f, xvars, aut, ax, **kw)
    plt.xlabel(xvars[0])
    plt.ylabel(xvars[1])
    # plt.savefig('essential_primes.pdf')


def test_cyclic_core_with_care_set():
    aut = _fol.Context()
    aut.declare(x=(0, 17))
    # cover = {True}
    s = '(x < 15)'
    f = aut.add_expr(s)
    s = '(x < 15)'
    care_set = aut.add_expr(s)
    cov.cyclic_core(f, care_set, aut)


def test_cyclic_core():
    aut = _fol.Context()
    aut.declare(x=(0, 4), y=(0, 4), z=(0, 4))
    # cover = single prime
    s = r'(x < 3) /\ (y = 2)'
    f = aut.add_expr(s)
    care_set = aut.true
    cov.cyclic_core(f, care_set, aut)
    # cover = 2 primes
    s = r'(x <= 2) \/ (y <= 2)'
    f = aut.add_expr(s)
    care_set = aut.true
    cov.cyclic_core(f, care_set, aut)
    # no cyclic core
    s = (
        r'('
        r'(0 <= x  /\  x <= 1) \/ '
        r'(0 <= x  /\  x <= 1  /\  1 <= y  /\  y <= 3) \/ '
        r'(3 <= x  /\  x <= 4) \/ '
        r'(3 <= x  /\  x <= 4  /\  1 <= y  /\  y <= 3) \/ '
        r'(0 <= y  /\  y <= 1) \/ '
        r'(0 <= y  /\  y <= 1  /\  1 <= x  /\  x <= 3) \/ '
        r'(3 <= y  /\  y <= 4) \/ '
        r'(3 <= y  /\  y <= 4  /\  1 <= x  /\  x <= 3) '
        r') /\ (0 <= x) /\ (x <= 4) /\ '
        r'(0 <= y) /\ (y <= 4) ')
    f = aut.add_expr(s)
    care_set = aut.true
    cov.cyclic_core(f, care_set, aut)
    # no cyclic core
    s = (
        r'('
        r'(0 <= x  /\  x <= 3  /\  0 <= y  /\  y <= 1) \/ '
        r'(1 <= x  /\  x <= 4  /\  0 <= y  /\  y <= 1) \/ '
        r'(0 <= x  /\  x <= 3  /\  3 <= y  /\  y <= 4) \/ '
        r'(1 <= x  /\  x <= 4  /\  3 <= y  /\  y <= 4) \/ '
        r'(0 <= x  /\  x <= 1  /\  0 <= y  /\  y <= 3) \/ '
        r'(0 <= x  /\  x <= 1  /\  1 <= y  /\  y <= 4) \/ '
        r'(3 <= x  /\  x <= 4  /\  0 <= y  /\  y <= 3) \/ '
        r'(3 <= x  /\  x <= 4  /\  1 <= y  /\  y <= 4) '
        r') /\ (0 <= x) /\ (x <= 4) /\ '
        r'(0 <= y) /\ (y <= 4) ')
    f = aut.add_expr(s)
    care_set = aut.true
    cov.cyclic_core(f, care_set, aut)
    # has cyclic core
    logger = logging.getLogger('omega.symbolic.cover')
    old_level = logger.getEffectiveLevel()
    # in order to test `_print_cyclic_core`
    logger.setLevel(logging.INFO)
    s = (
        r'('
        r'(z = 1  /\  y = 0)  \/ '
        r'(x = 0  /\  z = 1)  \/ '
        r'(y = 1  /\  x = 0)  \/ '
        r'(y = 1  /\  z = 0)  \/ '
        r'(x = 1  /\  z = 0)  \/ '
        r'(x = 1  /\  y = 0) '
        r') /\ (0 <= x  /\  x <= 1  /\ '
        r'0 <= y  /\  y <= 1  /\ '
        r'0 <= z  /\  z <= 1) ')
    f = aut.add_expr(s)
    care_set = aut.true
    cov.cyclic_core(f, care_set, aut)
    logger.setLevel(old_level)


def test_cyclic_core_recursion():
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
    cover = cov.minimize(f, care_set, fol)
    n = fol.count(cover)
    assert n == 6, n
    # print(fol.to_expr(f, show_dom=True))


def test_needs_unfloors():
    """Floors shrinks both primes to one smaller implicant.

    The returned cover is a minimal cover, so the
    assertion `_covers` in the function `cover.minimize` passes.
    However, the returned cover is not made of primes from
    the set `y` computed by calling `prime_implicants`.

    Finding the primes takes into account the care set.
    The resulting covering problem is such that shrinking happens.
    Therefore, unfloors is necessary in this problem.
    """
    fol = _fol.Context()
    fol.declare(x=(0, 1), y=(0, 1))
    f = fol.add_expr(r'x = 0 /\ y = 0')
    care = fol.add_expr(r'''
        \/ (x = 0 /\ y = 0)
        \/ (x = 1 /\ y = 1)
        ''')
    cover = cov.minimize(f, care, fol)
    implicants = list(fol.pick_iter(cover))
    assert len(implicants) == 1, implicants
    (d,) = implicants
    d_1 = dict(a_x=0, b_x=1, a_y=0, b_y=0)
    d_2 = dict(a_x=0, b_x=0, a_y=0, b_y=1)
    assert d == d_1 or d == d_2, d
    # s = cov.dumps_cover(cover, f, care, fol)
    # print(s)


def test_max_transpose():
    fol = _fol.Context()
    # `p'` serves as `u`
    dvars = {'p': (0, 4), 'q': (0, 4), "p_cp": (0, 4)}
    fol.declare(**dvars)
    s = r'(p = 2) \/ (p = 4)'
    p_is_prime = fol.add_expr(s)
    s = r'(p = 1) \/ (p = 3)'
    p_is_signature = fol.add_expr(s)
    p_to_q = {'p': 'q'}
    # we use intervals `0..p` as literals
    px = dict(p=dict(a='0', b='p'))
    qx = dict(p=dict(a='0', b='q'))
    u_leq_p = fol.add_expr("p_cp <= p")
    p_leq_u = fol.add_expr("p <= p_cp")
    p_leq_q = fol.add_expr("p <= q")
    p_eq_q = fol.add_expr("p = q")  # /\ (0 = 0)
    prm = lat.Parameters()
    prm._px = px
    prm._qx = qx
    prm.u_leq_p = u_leq_p
    prm.p_leq_u = p_leq_u
    prm.p_leq_q = p_leq_q
    prm.p_eq_q = p_eq_q
    prm.p_to_q = p_to_q
    prm.p_vars = {'p'}
    prm.q_vars = {'q'}
    prm.u_vars = {'p_cp'}
    prm.p_to_u = {'p': 'p_cp'}
    bab = cov._BranchAndBound(prm, fol)
    max_tau_x = cov._max_transpose(
        p_is_signature, p_is_prime, bab, fol)
    s = 'p = 3'
    max_tau_x_ = fol.add_expr(s)
    assert max_tau_x == max_tau_x_


def test_transpose():
    fol = _fol.Context()
    dvars = {'p': (0, 4), 'q': (0, 4), "p_cp": (0, 4)}
    fol.declare(**dvars)
    s = r'(p = 1) \/ (p = 2) \/ (p = 4)'
    p_is_prime = fol.add_expr(s)
    s = r'(p = 1) \/ (p = 3)'
    p_is_signature = fol.add_expr(s)
    p_to_q = {'p': 'q'}
    p_leq_q = fol.add_expr("p <= q")
    u_leq_p = fol.add_expr("p_cp <= p")
    p_leq_u = fol.add_expr("p <= p_cp")
    prm = lat.Parameters()
    prm.u_leq_p = u_leq_p
    prm.p_leq_u = p_leq_u
    prm.p_leq_q = p_leq_q
    prm.p_to_q = p_to_q
    prm.p_vars = {'p'}
    prm.q_vars = {'q'}
    prm.u_vars = {'p_cp'}
    prm.p_to_u = {'p': 'p_cp'}
    bab = cov._BranchAndBound(prm, fol)
    tau = cov._floor(
        p_is_signature, p_is_prime, bab, fol)
    s = r'p = 1 \/ p = 3'
    tau_ = fol.add_expr(s)
    assert tau == tau_


def test_contains_covered():
    fol = _fol.Context()
    fol.declare(p_cp=(0, 4), p=(0, 4), q=(0, 4))
    s = r'p_cp = 1 \/ p_cp = 2 \/ p_cp = 5'
    u_is_signature = fol.add_expr(s)
    prm = lat.Parameters()
    prm.p_vars = {'p'}
    prm.q_vars = {'q'}
    prm.u_vars = {'p_cp'}
    prm.p_to_q = {'p': 'q'}
    prm.u_leq_p = fol.add_expr('p_cp <= p')
    prm.p_leq_q = fol.add_expr('p <= q')
    # prm.p_to_u = {'p': 'u'}
    p_like_q = cov._contains_covered(
        u_is_signature, prm.u_leq_p, prm, fol)
    supp = fol.support(p_like_q)
    # pprint.pprint(list(fol.pick_iter(p_like_q, care_vars=supp)))
    s = (
        r'((q >= 1) => (p >= 1)) /\ '
        r'((q >= 2) => (p >= 2)) /\ '
        '((q >= 5) => (p >= 5))')
    p_like_q_ = fol.add_expr(s)
    assert p_like_q == p_like_q_


def test_maxima():
    prm = lat.Parameters()
    fol, _ = setup_aut(5, 5)
    s = r'x = 1 \/ x = 3 \/ x = 4'
    u = fol.add_expr(s)
    # x <= y
    s = r'(x = 1 /\ y = 1) \/ (x = 1 /\ y = 3)'
    prm.p_leq_q = fol.add_expr(s)
    prm.p_vars = {'x'}
    prm.q_vars = {'y'}
    prm.p_to_q = {'x': 'y'}
    r = stx.conj(f'{pj} = {qj}'
                      for pj, qj in prm.p_to_q.items())
    prm.p_eq_q = fol.add_expr(r)
    t0 = time.perf_counter()
    m = cov._maxima(u, prm, fol)
    t1 = time.perf_counter()
    dt = t1 - t0
    log.info(f'`maxima` time (sec): {dt:1.2f}')
    # print result
    gen = fol.pick_iter(m, care_vars=['x'])
    c = list(gen)
    log.info(c)


def test_lower_bound():
    x, y, p_leq_q, p_to_q, fol = simple_covering_problem()
    n = cov._lower_bound(x, y, p_leq_q, p_to_q, fol)
    assert n >= 2, n
    assert n <= 2, n
    n_ = cov._lower_bound_naive(x, y, p_leq_q, p_to_q, fol)
    assert n == n_, (n, n_)


def test_upper_bound():
    x, y, p_leq_q, p_to_q, fol = simple_covering_problem()
    n = cov._upper_bound(x, y, p_leq_q, p_to_q, fol)
    assert n >= 2, n
    assert n <= 4, n
    n_ = cov._upper_bound_naive(x, y, p_leq_q, p_to_q, fol)
    assert n == n_, (n, n_)


def test_independent_set():
    x, y, p_leq_q, p_to_q, fol = simple_covering_problem()
    z, k = cov._independent_set(
        x, y, p_leq_q, p_to_q, fol, only_size=False)
    k_ = fol.count(z)
    assert k_ == k, (k_, k)
    z, k_ = cov._independent_set(
        x, y, p_leq_q, p_to_q, fol, only_size=True)
    assert k_ == k, (k_, k)
    assert z is None, z


def test_some_cover():
    x, y, p_leq_q, p_to_q, fol = simple_covering_problem()
    z, k = cov._some_cover(
        x, y, p_leq_q, p_to_q, fol, only_size=False)
    k_ = fol.count(z)
    assert k_ == k, (k_, k)
    z, k_ = cov._some_cover(
        x, y, p_leq_q, p_to_q, fol, only_size=True)
    assert k_ == k, (k_, k)
    assert z is None, z


def simple_covering_problem():
    fol = _fol.Context()
    vrs = {'p': (0, 4), 'q': (0, 4), "p'": (0, 4)}
    # signatures
    fol.declare(**vrs)
    s = r'(p = 1) \/ (p = 2) \/ (p = 4)'
    x = fol.add_expr(s)
    # primes
    s = r'(p = 2) \/ (p = 3) \/ (p = 4) \/ (p = 5)'
    y = fol.add_expr(s)
    p_to_q = dict(p='q')
    s = '''\
           ((p < 4) /\\ (q < 4) /\\ (p <= q))
        \\/ ((p >= 4) /\\ (q >= 4) /\\ (p <= q))
    '''
    p_leq_q = fol.add_expr(s)
    return x, y, p_leq_q, p_to_q, fol


def test_partial_order():
    fol = _fol.Context()
    fol.declare(
        x=(0, 4), w=(0, 4), w_cp=(0, 4),
        t=(0, 4), t_cp=(0, 4))
    px = dict(x=dict(a='w', b='t'))
    u_leq_p, p_leq_u = lat.partial_order(px, fol)
    s = r'(w <= w_cp) /\ (t_cp <= t)'
    u_leq_p_ = fol.add_expr(s)
    assert u_leq_p == u_leq_p_
    s = r'(w_cp <= w) /\ (t <= t_cp)'
    p_leq_u_ = fol.add_expr(s)
    assert p_leq_u == p_leq_u_


def test_essential_orthotopes():
    fol, prm = setup_orthotope_vars()
    # x in support(f)
    f = fol.add_expr(r'1 < x  /\  x < 3')
    r = lat.essential_orthotopes(f, prm, fol)
    s = r'''
        /\ px = 2  /\  qx = 2
        /\ py = 0  /\  qy = 15
        '''
    r_ = fol.add_expr(s)
    assert r == r_, pprint.pformat(list(fol.pick_iter(r)))
    # x, y in support(f)
    s = r'''
        /\ -1 <= x  /\  x < 3
        /\ 4 < y  /\  y <= 17
        '''
    f = fol.add_expr(s)
    r = lat.essential_orthotopes(f, prm, fol)
    s = r'''
        /\ px = 0  /\  qx = 2
        /\ py = 5  /\  qy = 15
        '''
    r_ = fol.add_expr(s)
    assert r == r_, pprint.pformat(list(fol.pick_iter(r)))


def test_prime_orthotopes():
    fol, prm = setup_orthotope_vars()
    s = r'''
        /\ ax <= px  /\  qx <= bx
        /\ ay <= py  /\  qy <= by
        '''
    p_leq_q = fol.add_expr(s)
    s = r'''
        /\ ax = px  /\  qx = bx
        /\ ay = py  /\  qy = by
        '''
    p_eq_q = fol.add_expr(s)
    # x in support(f)
    f = fol.add_expr(r'2 <= x  /\  x <= 4')
    r = lat.prime_implicants(f, prm, fol)
    s = r'''
        /\ 2 = px  /\  qx = 4
        /\ 0 = py  /\  qy = 15
        '''
    r_ = fol.add_expr(s)
    assert r == r_, fol.count(r)  # pprint.pformat(list(fol.pick_iter(r)))
    # x, y in support(f)
    f = fol.add_expr(r'1 <= x  /\  x <= 3  /\  y <= 3')
    r = lat.prime_implicants(f, prm, fol)
    s = r'''
        /\ 1 = px  /\  qx = 3
        /\ 0 = py  /\  qy = 3
        '''
    r_ = fol.add_expr(s)
    assert r == r_, pprint.pformat(list(fol.pick_iter(r)))


def test_implicant_orthotopes():
    fol, prm = setup_orthotope_vars()
    # x in support(f)
    f = fol.add_expr('x < 2')
    r = lat._implicant_orthotopes(f, prm, fol)
    s = r'''
        /\ 0 <= px  /\  px <= qx  /\  qx < 2
        /\ 0 <= py  /\  py <= qy  /\  qy <= 15
        '''
    r_ = fol.add_expr(s)
    assert r == r_, fol.support(r)
    s = r'''
        /\ 0 <= px  /\  px <= qx  /\  qx < 2
        /\ 0 <= py  /\  py <= qy  /\  qy <= 14
        '''
    r_ = fol.add_expr(s)
    assert r != r_, fol.support(r)
    # x, y in support(f)
    f = fol.add_expr(r'x < 2  /\  y < 3')
    r = lat._implicant_orthotopes(f, prm, fol)
    s = r'''
        /\ 0 <= px  /\  px <= qx  /\  qx < 2
        /\ 0 <= py  /\  py <= qy  /\  qy < 3
        '''
    r_ = fol.add_expr(s)
    assert r == r_, fol.support(r)
    s = r'''
        /\ 0 <= px  /\  px <= qx  /\  qx < 2
        /\ 0 <= py  /\  py <= qy  /\  qy < 2
        '''
    r_ = fol.add_expr(s)
    assert r != r_, fol.support(r)


def setup_orthotope_vars():
    fol = _fol.Context()
    fol.declare(
        x=(0, 5), y=(2, 14),
        px=(0, 5), qx=(0, 5),
        py=(2, 14), qy=(2, 14),
        ax=(0, 5), bx=(0, 5),
        ay=(2, 14), by=(2, 14),)
    xvars = ['x', 'y']
    px = dict(x=dict(a='px', b='qx'),
               y=dict(a='py', b='qy'))
    qx = dict(x=dict(a='ax', b='bx'),
              y=dict(a='ay', b='by'))
    prm = lat.Parameters()
    prm.x_vars = xvars
    prm._px = px
    prm._qx = qx
    prm.p_to_q = dict(px='ax', py='ay', qx='bx', qy='by')
    prm.p_vars = set(prm.p_to_q)
    prm.q_vars = set(prm.p_to_q.values())
    varmap = lat.parameter_varmap(px, qx)
    prm.p_leq_q = lat.subseteq(varmap, fol)
    prm.p_eq_q = lat.eq(varmap, fol)
    return fol, prm


def test_none_covered():
    fol, prm = setup_aut()
    cover = fol.add_expr(r'a_x = 0  /\  b_x = 5')
    # some x are covered
    f = fol.add_expr(r'5 <= x /\ x <= 10')
    r = cov._none_covered(
        cover, f, prm, fol)
    assert r is False, r
    # no x is covered
    f = fol.add_expr(r'6 <= x /\ x <= 10')
    r = cov._none_covered(
        cover, f, prm, fol)
    assert r is True, r


def test_covers():
    fol, prm = setup_aut()
    # set it here to avoid calling `subseteq` from
    # `setup_aut` because it will violate unit testing
    p_leq_q = lat.subseteq(prm._varmap, fol)
    prm.p_leq_q = p_leq_q
    cover = fol.add_expr(r'a_x = 0  /\  b_x = 5')
    # not covered
    f = fol.add_expr(r'1 <= x  /\  x <= 6')
    r = cov._covers(cover, f, prm, fol)
    assert r is False, r
    r_ = cov._covers_naive(cover, f, prm, fol)
    assert r == r_, (r, r_)
    # covered
    f = fol.add_expr(r'0 <= x  /\  x <= 4')
    r = cov._covers(cover, f, prm, fol)
    assert r is True, r
    r_ = cov._covers_naive(cover, f, prm, fol)
    assert r == r_, (r, r_)


def test_concretize_implicants():
    fol, prm = setup_aut()
    impl = fol.add_expr(
        r'0 <= a_x  /\  a_x <= 3  /\ '
        r'1 <= b_x  /\  b_x <= 6 ')
    r = cov._concretize_implicants(impl, prm, fol)
    r_ = fol.add_expr(r'0 <= x  /\  x <= 6')
    assert r == r_, (r, r_)


def test_embed_as_implicants():
    fol, prm = setup_aut()
    prm._px = dict(x=prm._px['x'])  # restrict keys
    u = fol.add_expr(r'2 <= x  /\  x <= 9')
    r = lat.embed_as_implicants(u, prm, fol)
    r_ = lat._embed_as_implicants_naive(u, prm._px, fol)
    assert r == r_, (r, r_)
    v = fol.add_expr(
        r'(a_x = 2  /\  b_x = 2) \/'
        r'(a_x = 3  /\  b_x = 3) \/'
        r'(a_x = 4  /\  b_x = 4) \/'
        r'(a_x = 5  /\  b_x = 5) \/'
        r'(a_x = 6  /\  b_x = 6) \/'
        r'(a_x = 7  /\  b_x = 7) \/'
        r'(a_x = 8  /\  b_x = 8) \/'
        r'(a_x = 9  /\  b_x = 9)')
    assert r == v


def test_orthotope_singleton():
    fol, prm = setup_aut()
    r = lat._orthotope_singleton(prm._px, fol)
    d = dict(a_x=3, b_x=2, a_y=0, b_y=3)
    r = fol.let(d, r)
    assert r == fol.false
    r = lat._orthotope_singleton(prm._qx, fol)
    d = dict(u_x=1, v_x=1, u_y=10, v_y=10)
    r = fol.let(d, r)
    assert r == fol.true


def test_orthotope_nonempty():
    fol, prm = setup_aut()
    r = lat._orthotope_nonempty(prm._px, fol)
    d = dict(a_x=3, b_x=2, a_y=0, b_y=3)
    r = fol.let(d, r)
    assert r == fol.false
    r = lat._orthotope_nonempty(prm._qx, fol)
    d = dict(u_x=0, v_x=6, u_y=0, v_y=10)
    r = fol.let(d, r)
    assert r == fol.true


def test_orthotope_contains_x():
    aut, prm = setup_aut(15, 15)
    u = lat.x_in_implicant(prm, aut)
    values = dict(x=2, y=2,
                  a_x=0, b_x=10,
                  a_y=1, b_y=2)
    r = aut.let(values, u)
    assert r == aut.true, r
    d = prm._varmap
    u = lat.subseteq(d, aut)
    values = dict(
        a_x=0, b_x=3, a_y=1, b_y=2,
        u_x=0, v_x=5, u_y=0, v_y=2)
    r = aut.let(values, u)
    assert r == aut.true, r
    values = dict(
        a_x=0, b_x=3, a_y=1, b_y=2,
        u_x=0, v_x=2, u_y=0, v_y=2)
    r = aut.let(values, u)
    assert r == aut.false, r


def test_orthotope_subseteq():
    fol, prm = setup_aut()
    varmap = prm._varmap
    r = lat.subseteq(varmap, fol)
    d = dict(a_x=1, b_x=2, a_y=0, b_y=3)
    r = fol.let(d, r)
    d = dict(u_x=1, v_x=1, u_y=2, v_y=3)
    r = fol.let(d, r)
    assert r == fol.false
    r = lat.subseteq(varmap, fol)
    d = dict(a_x=1, b_x=2, a_y=0, b_y=3)
    r = fol.let(d, r)
    d = dict(u_x=0, v_x=6, u_y=0, v_y=10)
    r = fol.let(d, r)
    assert r == fol.true


def test_orthotope_eq():
    fol, prm = setup_aut()
    varmap = prm._varmap
    r = lat.eq(varmap, fol)
    r_ = fol.add_expr(
        r'a_x = u_x /\ b_x = v_x /\ '
        r'a_y = u_y /\ b_y = v_y')
    assert r == r_, (r, r_)
    d = dict(a_x=1, b_x=2, a_y=0, b_y=3)
    r = fol.let(d, r)
    d = dict(u_x=4, v_x=6, u_y=7, v_y=10)
    r = fol.let(d, r)
    assert r == fol.false
    r = lat.eq(varmap, fol)
    d = dict(a_x=1, b_x=2, a_y=0, b_y=3)
    r = fol.let(d, r)
    d = dict(u_x=1, v_x=2, u_y=0, v_y=3)
    r = fol.let(d, r)
    assert r == fol.true


def test_orthotopes_intersect():
    fol, prm = setup_aut()
    r = lat.implicants_intersect(prm, fol)
    d = dict(a_x=1, b_x=2, a_y=0, b_y=3)
    r = fol.let(d, r)
    d = dict(u_x=4, v_x=6, u_y=7, v_y=10)
    r = fol.let(d, r)
    assert r == fol.false
    r = lat.implicants_intersect(prm, fol)
    d = dict(a_x=1, b_x=2, a_y=0, b_y=3)
    r = fol.let(d, r)
    d = dict(u_x=0, v_x=6, u_y=7, v_y=10)
    r = fol.let(d, r)
    assert r == fol.false
    r = lat.implicants_intersect(prm, fol)
    d = dict(a_x=1, b_x=2, a_y=0, b_y=3)
    r = fol.let(d, r)
    d = dict(u_x=0, v_x=6, u_y=1, v_y=2)
    r = fol.let(d, r)
    assert r == fol.true


def setup_aut(xmax=15, ymax=15):
    fol = _fol.Context()
    fol.bdd.configure(reordering=True)
    # CAUTION: remember that type hints (safety)
    # needs to be added as care set
    fol.declare(x=(0, xmax), y=(0, ymax))
    x_vars = ['x', 'y']
    p_table = lat._parameter_table(
        x_vars, fol.vars, a_name='a', b_name='b')
    q_table = lat._parameter_table(
        x_vars, fol.vars, a_name='u', b_name='v')
    fol.declare(**p_table)
    fol.declare(**q_table)
    px = lat._map_vars_to_parameters(
        x_vars, a_name='a', b_name='b')
    qx = lat._map_vars_to_parameters(
        x_vars, a_name='u', b_name='v')
    varmap = lat.parameter_varmap(px, qx)
    p_to_q = lat._renaming_between_parameters(px, qx)
    prm = lat.Parameters()
    prm.x_vars = x_vars
    prm.p_vars = set(p_table)
    prm.q_vars = set(q_table)
    prm.p_to_q = p_to_q
    prm._px = px
    prm._qx = qx
    prm._varmap = varmap
    return fol, prm


def robots_example(fol):
    """Return cooperative winning set from ACC'16 example."""
    c = [
        r'(x = 0) /\ (y = 4)',
        r'(x = 0) /\ (y = 5)',
        r'(x = 0) /\ (y = 2)',
        r'(x = 0) /\ (y = 3)',
        r'(x = 0) /\ (y = 6)',
        r'(x = 0) /\ (y = 7)',
        r'(x = 1) /\ (y = 0)',
        r'(x = 1) /\ (y = 2)',
        r'(x = 1) /\ (y = 4)',
        r'(x = 1) /\ (y = 6)',
        r'(x = 1) /\ (y = 5)',
        r'(x = 1) /\ (y = 3)',
        r'(x = 1) /\ (y = 7)',
        r'(x = 2) /\ (y = 0)',
        r'(x = 2) /\ (y = 1)',
        r'(x = 2) /\ (y = 6)',
        r'(x = 2) /\ (y = 7)',
        r'(x = 3) /\ (y = 0)',
        r'(x = 3) /\ (y = 2)',
        r'(x = 3) /\ (y = 6)',
        r'(x = 3) /\ (y = 1)',
        r'(x = 3) /\ (y = 7)',
        r'(x = 4) /\ (y = 0)',
        r'(x = 4) /\ (y = 1)',
        r'(x = 4) /\ (y = 2)',
        r'(x = 4) /\ (y = 3)',
        r'(x = 4) /\ (y = 6)',
        r'(x = 4) /\ (y = 7)',
        r'(x = 5) /\ (y = 0)',
        r'(x = 5) /\ (y = 2)',
        r'(x = 5) /\ (y = 4)',
        r'(x = 5) /\ (y = 6)',
        r'(x = 5) /\ (y = 1)',
        r'(x = 5) /\ (y = 3)',
        r'(x = 5) /\ (y = 7)']
    s = stx.disj(c)
    u = fol.add_expr(s)
    return u


def test_dumps_cover():
    fol = _fol.Context()
    fol.declare(x=(0, 4), y=(-5, 9))
    # care = TRUE
    s = r'2 <= x  /\  x <= 4'
    u = fol.add_expr(s)
    care = fol.true
    cover = cov.minimize(u, care, fol)
    s = cov.dumps_cover(cover, u, care, fol)
    s_ = (
        '(* `f` depends on:  x *)\n'
        '(* `care` depends on:   *)\n'
        '(* The minimal cover is: *)\n'
        r'(x \in 2 .. 4)')
    assert s == s_, (s, s_)
    # care doesn't imply type hints
    s = cov.dumps_cover(
        cover, u, care, fol,
        show_dom=True)
    s_ = (
        '(* `f` depends on:  x *)\n'
        '(* `care` depends on:   *)\n'
        '(* The minimal cover is: *)\n'
        r'(x \in 2 .. 4)')
    assert s == s_, (s, s_)
    # with limits
    s = cov.dumps_cover(
        cover, u, care, fol,
        show_dom=True,
        show_limits=True)
    s_ = (
        '(* `f` depends on:  x *)\n'
        '(* `care` depends on:   *)\n'
        '(* The minimal cover is: *)\n'
        '/\\ x \\in 0 .. 7\n'
        '/\\ (x \\in 2 .. 4)')
    assert s == s_, (s, s_)
    # care = type hints
    care = tyh._conjoin_type_hints(['x', 'y'], fol)
    cover = cov.minimize(u, care, fol)
    s = cov.dumps_cover(
        cover, u, care, fol,
        show_dom=True)
    s_ = (
        '(* `f` depends on:  x *)\n'
        '(* `care` depends on:  x, y *)\n'
        '(* The minimal cover is: *)\n'
        '/\\ x \\in 0 .. 4\n'
        '/\\ y \\in -5 .. 9\n'
        '/\\ (x \\in 2 .. 4)\n'
        '/\\ care expression')
    assert s == s_, (s, s_)


def test_vertical_op():
    c = ['a', 'b', 'c']
    s = stx.vertical_op(c)
    s_ = '/\\ a\n/\\ b\n/\\ c'
    assert s == s_, (s, s_)
    c = ['/\\ a\n/\\ b\n/\\ c', 'd', 'e']
    s = stx.vertical_op(c)
    s_ = ('/\\ /\\ a\n'
          '   /\\ b\n'
          '   /\\ c\n'
          '/\\ d\n'
          '/\\ e')
    assert s == s_, (s, s_)
    c = ['/\\ a\n/\\ b\n/\\ c', 'd', 'e']
    s = stx.vertical_op(c, op='or')
    s_ = '\\/ /\\ a\n   /\\ b\n   /\\ c\n\\/ d\n\\/ e'
    assert s == s_, (s, s_)
    c = ['e']
    s = stx.vertical_op(c)
    s_ = c[0]
    assert s == s_, (s, s_)
    c = ['/\\ a\n/\\ b\n/\\ c']
    s = stx.vertical_op(c)
    s_ = c[0]
    assert s == s_, (s, s_)
    c = ['a', 'b', 'c']
    s = stx.vertical_op(c, op='and', latex=True)
    c = [s, 'd', 'e']
    s = stx.vertical_op(c, op='or', latex=True)
    s_ = r'''\begin{disj}
    \begin{conj}
        a \\
        b \\
        c
    \end{conj} \\
    d \\
    e
\end{disj}'''
    assert s == s_, (s, s_)


def test_list_orthotope_expr():
    fol = _fol.Context()
    fol.declare(
        x=(-4, 5), a_x=(-4, 5), b_x=(-4, 5),
        y=(-7, 15), a_y=(-7, 15), b_y=(-7, 15))
    px, _ = dummy_parameters()
    prm = lat.Parameters()
    prm._px = px
    f = fol.add_expr('x = 1')
    care = fol.true
    s = (
        r'(a_x = 2) /\ (2 <= b_x) /\ (b_x <= 3) '
        r'/\ (a_y = 1 ) /\ (b_y = 5)')
    cover = fol.add_expr(s)
    r = lat.list_expr(cover, prm, fol)
    r = set(r)
    r_ = {r'(x = 2) /\ (y \in 1 .. 5)',
          r'(x \in 2 .. 3) /\ (y \in 1 .. 5)'}
    assert r == r_, (r, r_)
    # simple syntax, for parsing back
    # (needed until able to parse `x \in a .. b` expressions)
    r = lat.list_expr(cover, prm, fol, simple=True)
    r = set(r)
    r_ = {r'(x = 2) /\ (1 <= y) /\ (y <= 5)',
          r'(2 <= x) /\ (x <= 3) /\ (1 <= y) /\ (y <= 5)'}
    assert r == r_, (r, r_)
    # clipping on, but nothing to clip
    r = lat.list_expr(cover, prm, fol, use_dom=True)
    r = set(r)
    r_ = {r'(x = 2) /\ (y \in 1 .. 5)',
          r'(x \in 2 .. 3) /\ (y \in 1 .. 5)'}
    assert r == r_, (r, r_)
    # clip using type hints
    s = (
        r'(a_x = -4) /\ (5 <= b_x)'
        r'/\ (a_y = 1 ) /\ (b_y = 5)')
    cover = fol.add_expr(s)
    r = lat.list_expr(cover, prm, fol, use_dom=True)
    r = set(r)
    r_ = {r'(y \in 1 .. 5)'}
    assert r == r_, (r, r_)
    # empty orthotopes
    s = (
        r'(a_x = -4) /\ (5 <= b_x)'
        r'/\ (a_y = 3 ) /\ (b_y = 1)')
    cover = fol.add_expr(s)
    with pytest.raises(AssertionError):
        lat.list_expr(cover, prm, fol, use_dom=True)
    with pytest.raises(AssertionError):
        lat.list_expr(cover, prm, fol)


def test_clip_subrange():
    ab = (6, 9)
    dom = (0, 10)
    r = tyh._clip_subrange(ab, dom, 'x')
    assert r == ab, (r, ab)
    ab = (-5, 9)
    dom = (0, 10)
    r = tyh._clip_subrange(ab, dom, 'x')
    r_ = (0, 9)
    assert r == r_, (r, r_)
    ab = (6, 15)
    dom = (0, 10)
    r = tyh._clip_subrange(ab, dom, 'x')
    r_ = (6, 10)
    assert r == r_, (r, r_)


def test_check_type_hint():
    hint = dict(dom=(0, 50), width=6, signed=True)
    with pytest.raises(AssertionError):
        tyh._check_type_hint(10, 0, hint, 'x')
    tyh._check_type_hint(2, 5, hint, 'y')


def test_care_implies_type_hints():
    fol = _fol.Context()
    fol.declare(x=(-4, 5), y=(-7, 15))
    f = fol.add_expr(r'0 < x  /\  x < 4')
    care = fol.add_expr(r'-2 <= y  /\  y <= 4')
    r = cov._care_implies_type_hints(f, care, fol)
    assert r is False, r
    care = fol.add_expr(
        r'1 <= x  /\  x <= 6  /\ '
        r'-2 <= y  /\  y <= 4')
    r = cov._care_implies_type_hints(f, care, fol)
    assert r is False, r
    care = fol.add_expr(
        r'1 <= x  /\  x <= 5  /\ '
        r'-2 <= y  /\  y <= 4')
    r = cov._care_implies_type_hints(f, care, fol)
    assert r is True, r


def test_f_implies_care():
    fol = _fol.Context()
    fol.declare(x=(-4, 5))
    f = fol.add_expr(r'0 < x  /\  x < 4')
    care = fol.add_expr(r'-2 <= x  /\  x <= 4')
    r = cov._f_implies_care(f, care, fol)
    assert r is True, r
    care = fol.add_expr(r'-2 <= x  /\  x <= 2')
    r = cov._f_implies_care(f, care, fol)
    assert r is False, r


def test_list_type_hints():
    with pytest.raises(AssertionError):
        tyh._list_type_hints(list(), 'whatever')
    table = dict(
        x=dict(type='int', dom=(-4, 5)),
        y=dict(type='int', dom=(-7, 15)))
    vrs = ['x', 'y']
    r = tyh._list_type_hints(vrs, table)
    r_ = [r'x \in -4 .. 5',
          r'y \in -7 .. 15']
    assert r == r_, (r, r_)


def test_list_limits():
    table = dict(
        x=dict(type='int', dom=(-4, 5), width=4, signed=True),
        y=dict(type='int', dom=(-7, 15), width=5, signed=True))
    r = tyh._list_limits(['x'], table)
    r_ = [r'x \in -8 .. 7']
    assert r == r_, (r, r_)
    r = tyh._list_limits(['x', 'y'], table)
    r_ = [r'x \in -8 .. 7', r'y \in -16 .. 15']
    assert r == r_, (r, r_)


def test_bitfield_limits():
    # positive
    hint = dict(width=1, signed=False, dom=(0, 0))
    r = tyh._bitfield_limits(hint)
    assert r == (0, 1), r
    hint = dict(width=2, signed=False, dom=(1, 2))
    r = tyh._bitfield_limits(hint)
    assert r == (0, 3), r
    hint = dict(width=10, signed=False, dom=(0, 12))
    r = tyh._bitfield_limits(hint)
    assert r == (0, 1_023), r
    # negative
    hint = dict(width=4, signed=False, dom=(-13, -2))
    r = tyh._bitfield_limits(hint)
    assert r == (-16, -1), r
    # signed
    hint = dict(width=1, signed=True)
    r = tyh._bitfield_limits(hint)
    assert r == (-1, 0), r
    hint = dict(width=2, signed=True)
    r = tyh._bitfield_limits(hint)
    assert r == (-2, 1), r
    hint = dict(width=10, signed=True)
    r = tyh._bitfield_limits(hint)
    assert r == (-512, 511), r


def test_conjoin_type_hints():
    fol = _fol.Context()
    fol.declare(x=(-4, 5), y=(-7, 15))
    vrs = ['x']
    u = tyh._conjoin_type_hints(vrs, fol)
    u_ = fol.add_expr(r'-4 <= x  /\  x <= 5')
    assert u == u_, (u, u_)
    vrs = ['y']
    u = tyh._conjoin_type_hints(vrs, fol)
    u_ = fol.add_expr(r'-7 <= y  /\  y <= 15')
    assert u == u_, (u, u_)
    vrs = ['x', 'y']
    u = tyh._conjoin_type_hints(vrs, fol)
    u_ = fol.add_expr(
        r'-4 <= x  /\  x <= 5 /\ '
        r'-7 <= y  /\  y <= 15')
    assert u == u_, (u, u_)


def test_format_range():
    r = tyh._format_range('wqd', 'g', 'k')
    r_ = r'wqd \in g .. k'
    assert r == r_, (r, r_)


def test_orthotopes_iter():
    fol = _fol.Context()
    fol.declare(p=(2, 9))
    # careful with the type hint
    u = fol.add_expr(r'(0 <= p) /\ (p <= 10)')
    c = list(lat._orthotopes_iter(u, fol))
    assert len(c) == 11, c


def test_setup_aux_vars():
    fol = _fol.Context()
    fol.declare(x=(-4, 5), y=(-7, 15))
    f = fol.add_expr('x = 2')
    care = fol.true
    prm = lat.setup_aux_vars(f, care, fol)
    vrs = prm.x_vars
    px = prm._px
    qx = prm._qx
    p_to_q = prm.p_to_q
    vrs_ = {'x'}
    assert vrs == vrs_, (vrs, vrs_)
    px_ = dict(x=dict(a='a_x', b='b_x'))
    assert px == px_, (px, px_)
    qx_ = dict(x=dict(a='u_x', b='v_x'))
    assert qx == qx_, (qx, qx_)
    p_to_q_ = dict(a_x='u_x', b_x='v_x')
    assert p_to_q == p_to_q_, (p_to_q, p_to_q_)


def test_parameter_table():
    vrs = ['x', 'y']
    table = dict(
        x=dict(type='int', dom=(-4, 5)),
        y=dict(type='int', dom=(-7, 15)),
        z=dict(type='bool'))
    t = lat._parameter_table(vrs, table, 'u', 'v')
    params = dict(u_x='x', v_x='x', u_y='y', v_y='y')
    for p, x in params.items():
        assert p in t, (p, t)
        dom = t[p]
        dom_ = table[x]['dom']
        assert dom == dom_, (dom, dom_)


def test_map_vars_to_parameters():
    x = ['x', 'y']
    px = lat._map_vars_to_parameters(x, 'a', 'b')
    px_ = dict(
        x=dict(a='a_x', b='b_x'),
        y=dict(a='a_y', b='b_y'))
    assert px == px_, (px, px_)


def test_map_parameters_to_vars():
    px, _ = dummy_parameters()
    d = lat._map_parameters_to_vars(px)
    d_ = dict(a_x='x', b_x='x',
              a_y='y', b_y='y')
    assert d == d_, (d, d_)


def test_collect_parameters():
    px, _ = dummy_parameters()
    c = lat.collect_parameters(px)
    c_ = {'a_x', 'b_x', 'a_y', 'b_y'}
    assert c == c_, (c, c_)


def test_parameter_varmap():
    px, qx = dummy_parameters()
    d = lat.parameter_varmap(px, qx)
    d_ = {('a_x', 'b_x'): ('u_x', 'v_x'),
          ('a_y', 'b_y'): ('u_y', 'v_y')}
    assert d == d_, (d, d_)


def test_renaming_between_parameters():
    px, qx = dummy_parameters()
    d = lat._renaming_between_parameters(px, qx)
    d_ = dict(
        a_x='u_x', b_x='v_x',
        a_y='u_y', b_y='v_y')
    assert d == d_, (d, d_)


def dummy_parameters():
    px = dict(
        x=dict(a='a_x', b='b_x'),
        y=dict(a='a_y', b='b_y'))
    qx = dict(
        x=dict(a='u_x', b='v_x'),
        y=dict(a='u_y', b='v_y'))
    return px, qx


def test_replace_prime():
    pvar = "x'"
    r = stx._replace_prime(pvar)
    assert r == "x_p", r
    with pytest.raises(AssertionError):
         stx._replace_prime("a'bc")
    with pytest.raises(AssertionError):
         stx._replace_prime("a'bc'")
    # identity
    var = "x"
    var_ = stx._replace_prime(var)
    assert var == var_, (var, var_)


def test_add_prime_like_too():
    table = dict(x=(-4, 5), y='bool')
    t = stx._add_prime_like_too(table)
    assert 'x' in t, t
    assert 'y' in t, t
    xp = stx._prime_like('x')
    yp = stx._prime_like('y')
    assert xp != 'x', xp
    assert yp != 'y', yp
    assert xp in t, (xp, t)
    assert yp in t, (yp, t)
    assert t['x'] == table['x'], t
    assert t['y'] == table['y'], t
    assert t[xp] == t['x'], t
    assert t[yp] == t['y'], t
    with pytest.raises(AssertionError):
        table["x'"] = tuple(table['x'])
        stx._add_prime_like_too(table)


def test_prime_like():
    var = 'x'
    pvar = stx._prime_like(var)
    assert pvar != var, (pvar, var)
    assert pvar == 'x_cp', pvar


def test_branch_and_bound_class():
    fol = _fol.Context()
    prm = lat.Parameters()
    bab = cov._BranchAndBound(prm, fol)
    bab.lower_bound = 15
    with pytest.raises(AssertionError):
        bab.upper_bound = 10
    bab.upper_bound = 20
    # only init for lower bound
    with pytest.raises(AssertionError):
        bab.lower_bound = 17
    with pytest.raises(AssertionError):
        bab.upper_bound = 10
    bab.upper_bound = 18


def run_expensive_functions_repeatedly():
    n = 10
    for i in range(n):
        test_cyclic_core()
        test_branching()
        test_orthotopes_using_robots_example()
        test_cyclic_core_using_robots_example()
        test_dumps_cover()
        test_essential_orthotopes()
        test_using_fol_context()
        test_implicant_orthotopes()


def profile_functions_above():
    import cProfile, pstats
    pr = cProfile.Profile()
    pr.enable()
    # run test functions
    d = globals()
    n = 0
    for k, v in d.items():
        if callable(v) and k.startswith('test_'):
            print(v)
            n += 1
            v()
    print(f'{n} test functions')
    pr.disable()
    ps = pstats.Stats(pr)
    ps = ps.strip_dirs()
    ps = ps.sort_stats('cumtime')
    ps.print_stats('cover_test', 10)


def configure_logging():
    h = logging.FileHandler('log.txt')
    formatter = logging.Formatter(
        '%(message)s')
    h.setFormatter(formatter)
    logger = logging.getLogger('omega.symbolic.cover')
    logger.setLevel(logging.INFO)
    logger.addHandler(h)
    logger = logging.getLogger('dd.bdd')
    logger.setLevel(logging.ERROR)
    logger.addHandler(h)


def main():
    test_orthotope_contains_x()
    test_orthotopes_using_robots_example()
    test_maxima()
    test_contains_covered()
    test_transpose()
    test_max_transpose()
    test_cyclic_core()
    test_cyclic_core_recursion()
    test_cyclic_core_using_robots_example()
    test_cyclic_core_with_care_set()
    test_branching()
    test_scaling_equality()
    test_using_fol_context()
    test_vertical_op()


if __name__ == '__main__':
    configure_logging()
    main()
