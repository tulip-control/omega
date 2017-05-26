"""Test `omega.symbolic.cover`."""
from __future__ import absolute_import
from __future__ import print_function
from itertools import cycle
import logging
import pprint
import time

# import matplotlib as mpl
# mpl.use('Agg')
# from matplotlib import pyplot as plt
plt = None  # uncomment if you want to plot
from nose.tools import assert_raises
from omega.logic import syntax as stx
from omega.symbolic.bdd import support_issubset
from omega.symbolic import fol as _fol

from omega.symbolic import cover as cov


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
    p_dom = cov._parameter_table(
        x_vars, aut.vars, a=params['pa'], b=params['pb'])
    q_dom = cov._parameter_table(
        x_vars, aut.vars, a=params['qa'], b=params['qb'])
    aut.declare(**p_dom)
    aut.declare(**q_dom)
    px = cov._parameter_variables(x_vars, a=params['pa'], b=params['pb'])
    qx = cov._parameter_variables(x_vars, a=params['qa'], b=params['qb'])
    p_to_q = cov._renaming_between_parameters(px, qx)
    x_as_x = {xj: dict(a=xj, b=xj) for xj in px}
    varmap = cov._parameter_varmap(px, x_as_x)
    log.info('Number of variables: {n}'.format(n=len(varmap)))
    u = cov._orthotope_subseteq(varmap, aut)
    #
    s = (
        '( '
        '(z = 1  /\  y <= 0)  \/ '
        '(x = 0  /\  z = 1)  \/ '
        '(y >= 1  /\  x <= 0)  \/ '
        '(y >= 1  /\  z <= 0)  \/ '
        '(x >= 1  /\  z <= 0)  \/ '
        '(x >= 1  /\  y <= 0) '
        ') ')
    f = aut.add_expr(s)
    cov._embed_as_implicants(f, px, aut)


def test_using_fol_context():
    c = _fol.Context()
    c.declare(x=(0, 5), y=(-4, 6))
    s = ('1 <= x /\ x <= 3 /\ -2 <= y /\ y <= 4')
    u = c.add_expr(s)
    care = c.true
    r = cov.minimize(u, care, c)
    s = cov.dumps_cover(r, u, care, c, show_limits=True)
    assert 'x \in 1 .. 3' in s, s
    assert 'y \in -2 .. 4' in s, s
    s_ = '''\
 /\ x \in 0 .. 7
 /\ y \in -8 .. 7
 /\ (x \in 1 .. 3) /\ (y \in -2 .. 4)'''
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
        '( '
        '(z = 1  /\  y <= 0)  \/ '
        '(x = 0  /\  z = 1)  \/ '
        '(y >= 1  /\  x <= 0)  \/ '
        '(y >= 1  /\  z <= 0)  \/ '
        '(x >= 1  /\  z <= 0)  \/ '
        '(x >= 1  /\  y <= 0) '
        ') ')
    f = aut.add_expr(s)
    s = (
        '0 <= x  /\  x <= 2  /\ '
        '0 <= y  /\  y <= 1  /\ '
        '0 <= z  /\  z <= 1 '
        )
    care_set = aut.add_expr(s)
    # care_set = aut.true
    cover = cov.minimize(f, care_set, aut)
    s = cov.dumps_cover(cover, f, care_set, aut)
    log.info(s)


def test_cost():
    r = cov._cost(None, '?', '?')
    assert r == float('inf'), r
    fol, _, _, _, p, _ = setup_aut()
    s = (
        '1 <= a_x /\ a_x <= 3 /\ b_x = 6 /\ '
        '2 <= a_y /\ a_y <= 5 /\ '
        '0 <= b_y /\ b_y <= 7')
    u = fol.add_expr(s)
    r = cov._cost(u, p, fol)
    assert r == 96, r


def test_cyclic_core_using_robots_example():
    aut, xvars, abx, uvx, ab_table, _ = setup_aut(15, 15)
    f = robots_example(aut)
    care_set = aut.true
    xcore, ycore, essential = cov.cyclic_core(f, care_set, aut)
    assert xcore == aut.false, xcore
    n_essential = aut.count(essential)
    k = aut.count(essential)
    assert n_essential == k, (n_essential, k)
    assert n_essential == 7, n_essential


def test_orthotopes_using_robots_example():
    aut, xvars, abx, uvx, ab_table, _ = setup_aut(15, 15)
    # this predicate is constructed by `contract_maker`
    # for the robots example in ACC 2016
    f = robots_example(aut)
    varmap = cov._parameter_varmap(abx, uvx)
    ab_leq_uv = cov._orthotope_subseteq(varmap, aut)
    ab_eq_uv = cov._orthotope_eq(varmap, aut)
    u = cov.prime_orthotopes(
        f, abx, uvx,
        ab_leq_uv, ab_eq_uv,
        aut, xvars)
    support = aut.support(u)
    assert support == set(ab_table), (support, ab_table)
    n_primes = aut.count(u)
    k = aut.count(u)
    assert n_primes == k, (n_primes, k)
    log.info('{n} prime implicants'.format(n=n_primes))
    u = cov.essential_orthotopes(f, abx, uvx, aut, xvars)
    support = aut.support(u)
    assert support == set(ab_table), (support, ab_table)
    n_essential = aut.count(u)
    k = aut.count(u)
    assert n_essential == k, (n_essential, k)
    log.info('{n} essential prime implicants'.format(n=n_essential))
    assert n_essential == 7, n_essential
    # result: all primes are essential in this example
    #
    care = aut.true
    s = cov.dumps_cover(u, f, care, aut)
    log.info(s)
    log.info('BDD has {n} nodes'.format(n=len(aut.bdd)))
    # confirm that essential orthotopes cover exactly `f`
    c = cov._list_orthotope_expr(u, abx, aut, simple=True)
    s = stx.disj(c)
    log.info(s)
    z = aut.add_expr(s)
    z = aut.exist(['a_x', 'b_x', 'a_y', 'b_y'], z)
    assert aut.support(z) == aut.support(f)
    assert z == f
    if plt is not None:
        _plot_orthotopes_for_robots_example(u, f, abx, xvars, aut)
    # pprint.pprint(aut.bdd.statistics())
    # pprint.pprint(aut.bdd.vars)
    log.info('{n} nodes in manager'.format(n=len(aut.bdd)))


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
    s = '(x < 3) /\ (y = 2)'
    f = aut.add_expr(s)
    care_set = aut.true
    cov.cyclic_core(f, care_set, aut)
    # cover = 2 primes
    s = '(x <= 2) \/ (y <= 2)'
    f = aut.add_expr(s)
    care_set = aut.true
    cov.cyclic_core(f, care_set, aut)
    # no cyclic core
    s = (
        '('
        '(0 <= x  /\  x <= 1) \/ '
        '(0 <= x  /\  x <= 1  /\  1 <= y  /\  y <= 3) \/ '
        '(3 <= x  /\  x <= 4) \/ '
        '(3 <= x  /\  x <= 4  /\  1 <= y  /\  y <= 3) \/ '
        '(0 <= y  /\  y <= 1) \/ '
        '(0 <= y  /\  y <= 1  /\  1 <= x  /\  x <= 3) \/ '
        '(3 <= y  /\  y <= 4) \/ '
        '(3 <= y  /\  y <= 4  /\  1 <= x  /\  x <= 3) '
        ') /\ (0 <= x) /\ (x <= 4) /\ '
        '(0 <= y) /\ (y <= 4) ')
    f = aut.add_expr(s)
    care_set = aut.true
    cov.cyclic_core(f, care_set, aut)
    # no cyclic core
    s = (
        '('
        '(0 <= x  /\  x <= 3  /\  0 <= y  /\  y <= 1) \/ '
        '(1 <= x  /\  x <= 4  /\  0 <= y  /\  y <= 1) \/ '
        '(0 <= x  /\  x <= 3  /\  3 <= y  /\  y <= 4) \/ '
        '(1 <= x  /\  x <= 4  /\  3 <= y  /\  y <= 4) \/ '
        '(0 <= x  /\  x <= 1  /\  0 <= y  /\  y <= 3) \/ '
        '(0 <= x  /\  x <= 1  /\  1 <= y  /\  y <= 4) \/ '
        '(3 <= x  /\  x <= 4  /\  0 <= y  /\  y <= 3) \/ '
        '(3 <= x  /\  x <= 4  /\  1 <= y  /\  y <= 4) '
        ') /\ (0 <= x) /\ (x <= 4) /\ '
        '(0 <= y) /\ (y <= 4) ')
    f = aut.add_expr(s)
    care_set = aut.true
    cov.cyclic_core(f, care_set, aut)
    # has cyclic core
    logger = logging.getLogger('omega.symbolic.cover')
    old_level = logger.getEffectiveLevel()
    # in order to test `_print_cyclic_core`
    logger.setLevel(logging.INFO)
    s = (
        '('
        '(z = 1  /\  y = 0)  \/ '
        '(x = 0  /\  z = 1)  \/ '
        '(y = 1  /\  x = 0)  \/ '
        '(y = 1  /\  z = 0)  \/ '
        '(x = 1  /\  z = 0)  \/ '
        '(x = 1  /\  y = 0) '
        ') /\ (0 <= x  /\  x <= 1  /\ '
        '0 <= y  /\  y <= 1  /\ '
        '0 <= z  /\  z <= 1) ')
    f = aut.add_expr(s)
    care_set = aut.true
    cov.cyclic_core(f, care_set, aut)
    logger.setLevel(old_level)


def test_cyclic_core_recursion():
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


def test_max_transpose():
    fol = _fol.Context()
    # `p'` serves as `u`
    dvars = {'p': (0, 4), 'q': (0, 4), "p_cp": (0, 4)}
    fol.declare(**dvars)
    s = '(p = 2) \/ (p = 4)'
    p_is_prime = fol.add_expr(s)
    s = '(p = 1) \/ (p = 3)'
    p_is_signature = fol.add_expr(s)
    p_to_q = {'p': 'q'}
    # we use intervals `0..p` as literals
    px = dict(p=dict(a='0', b='p'))
    qx = dict(p=dict(a='0', b='q'))
    u_leq_p = fol.add_expr("p_cp <= p")
    p_leq_u = fol.add_expr("p <= p_cp")
    p_leq_q = fol.add_expr("p <= q")
    p_eq_q = fol.add_expr("p = q")  # /\ (0 = 0)
    bab = cov._BranchAndBound(
        p_leq_q, p_leq_u, u_leq_p, p_eq_q,
        p_to_q, px, qx, fol)
    max_tau_x = cov._max_transpose(
        p_is_signature, p_is_prime, bab, fol)
    s = 'p = 3'
    max_tau_x_ = fol.add_expr(s)
    assert max_tau_x == max_tau_x_


def test_transpose():
    fol = _fol.Context()
    dvars = {'p': (0, 4), 'q': (0, 4), "p_cp": (0, 4)}
    fol.declare(**dvars)
    s = '(p = 1) \/ (p = 2) \/ (p = 4)'
    p_is_prime = fol.add_expr(s)
    s = '(p = 1) \/ (p = 3)'
    p_is_signature = fol.add_expr(s)
    p_to_q = {'p': 'q'}
    p_leq_q = fol.add_expr("p <= q")
    u_leq_p = fol.add_expr("p_cp <= p")
    p_leq_u = fol.add_expr("p <= p_cp")
    bab = cov._BranchAndBound(
        p_leq_q, p_leq_u, u_leq_p, None,
        p_to_q, None, None, fol)
    tau = cov._floor(
        p_is_signature, p_is_prime, bab, fol)
    s = 'p = 1 \/ p = 3'
    tau_ = fol.add_expr(s)
    assert tau == tau_


def test_contains_covered():
    fol = _fol.Context()
    fol.declare(p_cp=(0, 4), p=(0, 4), q=(0, 4))
    s = 'p_cp = 1 \/ p_cp = 2 \/ p_cp = 5'
    u_is_signature = fol.add_expr(s)
    u_leq_p = fol.add_expr('p_cp <= p')
    p_leq_q = fol.add_expr('p <= q')
    p_to_q = {'p': 'q'}
    # p_to_u = {'p': 'u'}
    bab = cov._BranchAndBound(
        p_leq_q, None, None, None, p_to_q, None, None, fol)
    p_like_q = cov._contains_covered(
        u_is_signature, u_leq_p, bab, fol)
    supp = fol.support(p_like_q)
    # pprint.pprint(list(fol.pick_iter(p_like_q, care_vars=supp)))
    s = (
        '((q >= 1) => (p >= 1)) /\ '
        '((q >= 2) => (p >= 2)) /\ '
        '((q >= 5) => (p >= 5))')
    p_like_q_ = fol.add_expr(s)
    assert p_like_q == p_like_q_


def test_maxima():
    fol, x_vars, ab, uv, _, _ = setup_aut(5, 5)
    s = 'x = 1 \/ x = 3 \/ x = 4'
    u = fol.add_expr(s)
    # x <= y
    s = '(x = 1 /\ y = 1) \/ (x = 1 /\ y = 3)'
    p_leq_q = fol.add_expr(s)
    p_to_q = {'x': 'y'}
    r = stx.conj('{pj} = {qj}'.format(pj=pj, qj=qj)
                      for pj, qj in p_to_q.items())
    p_eq_q = fol.add_expr(r)
    bab = cov._BranchAndBound(
        p_leq_q, None, None, p_eq_q, p_to_q,
        None, None, fol)
    t0 = time.time()
    m = cov._maxima(u, bab, fol)
    t1 = time.time()
    dt = t1 - t0
    log.info('`maxima` time (sec): {dt:1.2f}'.format(dt=dt))
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
    s = '(p = 1) \/ (p = 2) \/ (p = 4)'
    x = fol.add_expr(s)
    # primes
    s = '(p = 2) \/ (p = 3) \/ (p = 4) \/ (p = 5)'
    y = fol.add_expr(s)
    p_to_q = dict(p='q')
    s = '''\
           ((p < 4) /\ (q < 4) /\ (p <= q))
        \/ ((p >= 4) /\ (q >= 4) /\ (p <= q))
    '''
    p_leq_q = fol.add_expr(s)
    return x, y, p_leq_q, p_to_q, fol


def test_partial_order():
    fol = _fol.Context()
    fol.declare(
        x=(0, 4), w=(0, 4), w_cp=(0, 4),
        t=(0, 4), t_cp=(0, 4))
    px = dict(x=dict(a='w', b='t'))
    u_leq_p, p_leq_u = cov._partial_order(px, fol)
    s = '(w <= w_cp) /\ (t_cp <= t)'
    u_leq_p_ = fol.add_expr(s)
    assert u_leq_p == u_leq_p_
    s = '(w_cp <= w) /\ (t <= t_cp)'
    p_leq_u_ = fol.add_expr(s)
    assert p_leq_u == p_leq_u_


def test_essential_orthotopes():
    xvars, px, fol = setup_orthotope_vars()
    qx = dict(x=dict(a='ax', b='bx'),
              y=dict(a='ay', b='by'))
    # x in support(f)
    f = fol.add_expr('1 < x  /\  x < 3')
    r = cov.essential_orthotopes(f, px, qx, fol, xvars)
    s = '''
        /\ px = 2  /\  qx = 2
        /\ py = 0  /\  qy = 15
        '''
    r_ = fol.add_expr(s)
    assert r == r_, pprint.pformat(list(fol.pick_iter(r)))
    # x, y in support(f)
    s = '''
        /\ -1 <= x  /\  x < 3
        /\ 4 < y  /\  y <= 17
        '''
    f = fol.add_expr(s)
    r = cov.essential_orthotopes(f, px, qx, fol, xvars)
    s = '''
        /\ px = 0  /\  qx = 2
        /\ py = 5  /\  qy = 15
        '''
    r_ = fol.add_expr(s)
    assert r == r_, pprint.pformat(list(fol.pick_iter(r)))


def test_prime_orthotopes():
    xvars, px, fol = setup_orthotope_vars()
    qx = dict(x=dict(a='ax', b='bx'),
              y=dict(a='ay', b='by'))
    s = '''
        /\ ax <= px  /\  qx <= bx
        /\ ay <= py  /\  qy <= by
        '''
    p_leq_q = fol.add_expr(s)
    s = '''
        /\ ax = px  /\  qx = bx
        /\ ay = py  /\  qy = by
        '''
    p_eq_q = fol.add_expr(s)
    # x in support(f)
    f = fol.add_expr('2 <= x  /\  x <= 4')
    r = cov.prime_orthotopes(
        f, px, qx, p_leq_q, p_eq_q, fol, xvars)
    s = '''
        /\ 2 = px  /\  qx = 4
        /\ 0 = py  /\  qy = 15
        '''
    r_ = fol.add_expr(s)
    assert r == r_, pprint.pformat(list(fol.pick_iter(r)))
    # x, y in support(f)
    f = fol.add_expr('1 <= x  /\  x <= 3  /\  y <= 3')
    r = cov.prime_orthotopes(
        f, px, qx, p_leq_q, p_eq_q, fol, xvars)
    s = '''
        /\ 1 = px  /\  qx = 3
        /\ 0 = py  /\  qy = 3
        '''
    r_ = fol.add_expr(s)
    assert r == r_, pprint.pformat(list(fol.pick_iter(r)))


def test_implicant_orthotopes():
    xvars, abx, fol = setup_orthotope_vars()
    # x in support(f)
    f = fol.add_expr('x < 2')
    r = cov._implicant_orthotopes(f, abx, fol, xvars)
    s = '''
        /\ 0 <= px  /\  px <= qx  /\  qx < 2
        /\ 0 <= py  /\  py <= qy  /\  qy <= 15
        '''
    r_ = fol.add_expr(s)
    assert r == r_, fol.support(r)
    s = '''
        /\ 0 <= px  /\  px <= qx  /\  qx < 2
        /\ 0 <= py  /\  py <= qy  /\  qy <= 14
        '''
    r_ = fol.add_expr(s)
    assert r != r_, fol.support(r)
    # x, y in support(f)
    f = fol.add_expr('x < 2  /\  y < 3')
    r = cov._implicant_orthotopes(f, abx, fol, xvars)
    s = '''
        /\ 0 <= px  /\  px <= qx  /\  qx < 2
        /\ 0 <= py  /\  py <= qy  /\  qy < 3
        '''
    r_ = fol.add_expr(s)
    assert r == r_, fol.support(r)
    s = '''
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
    xvars = ('x', 'y')
    abx = dict(x=dict(a='px', b='qx'),
               y=dict(a='py', b='qy'))
    return xvars, abx, fol


def test_none_covered():
    fol, _, px, qx, _, _ = setup_aut()
    p_to_q = cov._renaming_between_parameters(px, qx)
    cover = fol.add_expr('a_x = 0  /\  b_x = 5')
    # some x are covered
    f = fol.add_expr('5 <= x /\ x <= 10')
    r = cov._none_covered(
        cover, f, p_to_q, px, qx, fol)
    assert r is False, r
    # no x is covered
    f = fol.add_expr('6 <= x /\ x <= 10')
    r = cov._none_covered(
        cover, f, p_to_q, px, qx, fol)
    assert r is True, r


def test_covers():
    fol, _, px, qx, _, _ = setup_aut()
    varmap = cov._parameter_varmap(px, qx)
    p_leq_q = cov._orthotope_subseteq(varmap, fol)
    p_to_q = cov._renaming_between_parameters(px, qx)
    cover = fol.add_expr('a_x = 0  /\  b_x = 5')
    # not covered
    f = fol.add_expr('1 <= x  /\  x <= 6')
    r = cov._covers(
        cover, f, p_leq_q,
        p_to_q, px, fol)
    assert r is False, r
    r_ = cov._covers_naive(cover, f, px, fol)
    assert r == r_, (r, r_)
    # covered
    f = fol.add_expr('0 <= x  /\  x <= 4')
    r = cov._covers(
        cover, f, p_leq_q,
        p_to_q, px, fol)
    assert r is True, r
    r_ = cov._covers_naive(cover, f, px, fol)
    assert r == r_, (r, r_)


def test_concretize_implicants():
    fol, _, px, _, _, _ = setup_aut()
    impl = fol.add_expr(
        '0 <= a_x  /\  a_x <= 3  /\ '
        '1 <= b_x  /\  b_x <= 6 ')
    r = cov._concretize_implicants(impl, px, fol)
    r_ = fol.add_expr('0 <= x  /\  x <= 6')
    assert r == r_, (r, r_)


def test_embed_as_implicants():
    fol, _, px, _, _, _ = setup_aut()
    u = fol.add_expr('2 <= x  /\  x <= 9')
    px = dict(x=px['x'])
    r = cov._embed_as_implicants(u, px, fol)
    r_ = cov._embed_as_implicants_naive(u, px, fol)
    assert r == r_, (r, r_)
    v = fol.add_expr(
        '(a_x = 2  /\  b_x = 2) \/'
        '(a_x = 3  /\  b_x = 3) \/'
        '(a_x = 4  /\  b_x = 4) \/'
        '(a_x = 5  /\  b_x = 5) \/'
        '(a_x = 6  /\  b_x = 6) \/'
        '(a_x = 7  /\  b_x = 7) \/'
        '(a_x = 8  /\  b_x = 8) \/'
        '(a_x = 9  /\  b_x = 9)')
    assert r == v


def test_orthotope_singleton():
    fol, _, px, qx, _, _ = setup_aut()
    r = cov._orthotope_singleton(px, fol)
    d = dict(a_x=3, b_x=2, a_y=0, b_y=3)
    r = fol.let(d, r)
    assert r == fol.false
    r = cov._orthotope_singleton(qx, fol)
    d = dict(u_x=1, v_x=1, u_y=10, v_y=10)
    r = fol.let(d, r)
    assert r == fol.true


def test_orthotope_nonempty():
    fol, _, px, qx, _, _ = setup_aut()
    r = cov._orthotope_nonempty(px, fol)
    d = dict(a_x=3, b_x=2, a_y=0, b_y=3)
    r = fol.let(d, r)
    assert r == fol.false
    r = cov._orthotope_nonempty(qx, fol)
    d = dict(u_x=0, v_x=6, u_y=0, v_y=10)
    r = fol.let(d, r)
    assert r == fol.true


def test_orthotope_contains_x():
    aut, _, abx, uvx, _, _ = setup_aut(15, 15)
    u = cov._orthotope_contains_x(abx, aut)
    values = dict(x=2, y=2,
                  a_x=0, b_x=10,
                  a_y=1, b_y=2)
    r = aut.let(values, u)
    assert r == aut.true, r
    d = cov._parameter_varmap(abx, uvx)
    u = cov._orthotope_subseteq(d, aut)
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
    fol, _, px, qx, _, _ = setup_aut()
    varmap = cov._parameter_varmap(px, qx)
    r = cov._orthotope_subseteq(varmap, fol)
    d = dict(a_x=1, b_x=2, a_y=0, b_y=3)
    r = fol.let(d, r)
    d = dict(u_x=1, v_x=1, u_y=2, v_y=3)
    r = fol.let(d, r)
    assert r == fol.false
    r = cov._orthotope_subseteq(varmap, fol)
    d = dict(a_x=1, b_x=2, a_y=0, b_y=3)
    r = fol.let(d, r)
    d = dict(u_x=0, v_x=6, u_y=0, v_y=10)
    r = fol.let(d, r)
    assert r == fol.true


def test_orthotope_eq():
    fol, _, px, qx, _, _ = setup_aut()
    varmap = cov._parameter_varmap(px, qx)
    r = cov._orthotope_eq(varmap, fol)
    r_ = fol.add_expr(
        'a_x = u_x /\ b_x = v_x /\ '
        'a_y = u_y /\ b_y = v_y')
    assert r == r_, (r, r_)
    d = dict(a_x=1, b_x=2, a_y=0, b_y=3)
    r = fol.let(d, r)
    d = dict(u_x=4, v_x=6, u_y=7, v_y=10)
    r = fol.let(d, r)
    assert r == fol.false
    r = cov._orthotope_eq(varmap, fol)
    d = dict(a_x=1, b_x=2, a_y=0, b_y=3)
    r = fol.let(d, r)
    d = dict(u_x=1, v_x=2, u_y=0, v_y=3)
    r = fol.let(d, r)
    assert r == fol.true


def test_orthotopes_intersect():
    fol, _, px, qx, _, _ = setup_aut()
    varmap = cov._parameter_varmap(px, qx)
    r = cov._orthotopes_intersect(varmap, fol)
    d = dict(a_x=1, b_x=2, a_y=0, b_y=3)
    r = fol.let(d, r)
    d = dict(u_x=4, v_x=6, u_y=7, v_y=10)
    r = fol.let(d, r)
    assert r == fol.false
    r = cov._orthotopes_intersect(varmap, fol)
    d = dict(a_x=1, b_x=2, a_y=0, b_y=3)
    r = fol.let(d, r)
    d = dict(u_x=0, v_x=6, u_y=7, v_y=10)
    r = fol.let(d, r)
    assert r == fol.false
    r = cov._orthotopes_intersect(varmap, fol)
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
    p_table = cov._parameter_table(x_vars, fol.vars, a='a', b='b')
    q_table = cov._parameter_table(x_vars, fol.vars, a='u', b='v')
    fol.declare(**p_table)
    fol.declare(**q_table)
    px = cov._parameter_variables(x_vars, a='a', b='b')
    qx = cov._parameter_variables(x_vars, a='u', b='v')
    return fol, x_vars, px, qx, p_table, q_table


def robots_example(fol):
    """Return cooperative winning set from ACC'16 example."""
    c = [
        '(x = 0) /\ (y = 4)',
        '(x = 0) /\ (y = 5)',
        '(x = 0) /\ (y = 2)',
        '(x = 0) /\ (y = 3)',
        '(x = 0) /\ (y = 6)',
        '(x = 0) /\ (y = 7)',
        '(x = 1) /\ (y = 0)',
        '(x = 1) /\ (y = 2)',
        '(x = 1) /\ (y = 4)',
        '(x = 1) /\ (y = 6)',
        '(x = 1) /\ (y = 5)',
        '(x = 1) /\ (y = 3)',
        '(x = 1) /\ (y = 7)',
        '(x = 2) /\ (y = 0)',
        '(x = 2) /\ (y = 1)',
        '(x = 2) /\ (y = 6)',
        '(x = 2) /\ (y = 7)',
        '(x = 3) /\ (y = 0)',
        '(x = 3) /\ (y = 2)',
        '(x = 3) /\ (y = 6)',
        '(x = 3) /\ (y = 1)',
        '(x = 3) /\ (y = 7)',
        '(x = 4) /\ (y = 0)',
        '(x = 4) /\ (y = 1)',
        '(x = 4) /\ (y = 2)',
        '(x = 4) /\ (y = 3)',
        '(x = 4) /\ (y = 6)',
        '(x = 4) /\ (y = 7)',
        '(x = 5) /\ (y = 0)',
        '(x = 5) /\ (y = 2)',
        '(x = 5) /\ (y = 4)',
        '(x = 5) /\ (y = 6)',
        '(x = 5) /\ (y = 1)',
        '(x = 5) /\ (y = 3)',
        '(x = 5) /\ (y = 7)']
    s = stx.disj(c)
    u = fol.add_expr(s)
    return u


def test_dumps_cover():
    fol = _fol.Context()
    fol.declare(x=(0, 4), y=(-5, 9))
    # care = TRUE
    s = '2 <= x  /\  x <= 4'
    u = fol.add_expr(s)
    care = fol.true
    cover = cov.minimize(u, care, fol)
    s = cov.dumps_cover(cover, u, care, fol)
    s_ = (
        '(x \in 2 .. 4)')
    assert s == s_, (s, s_)
    # care doesn't imply type hints
    s = cov.dumps_cover(
        cover, u, care, fol,
        show_dom=True)
    s_ = (
        '(x \in 2 .. 4)')
    assert s == s_, (s, s_)
    # with limits
    s = cov.dumps_cover(
        cover, u, care, fol,
        show_dom=True,
        show_limits=True)
    s_ = (
        ' /\ x \in 0 .. 7\n'
        ' /\ (x \in 2 .. 4)')
    assert s == s_, (s, s_)
    # care = type hints
    care = cov._conjoin_type_hints(['x', 'y'], fol)
    cover = cov.minimize(u, care, fol)
    s = cov.dumps_cover(
        cover, u, care, fol,
        show_dom=True)
    s_ = (
        ' /\ x \in 0 .. 4\n'
        ' /\ y \in -5 .. 9\n'
        ' /\ (x \in 2 .. 4)\n'
        ' /\ care expression')
    assert s == s_, (s, s_)


def test_vertical_op():
    c = ['a', 'b', 'c']
    s = cov._vertical_op(c)
    s_ = ' /\ a\n /\ b\n /\ c'
    assert s == s_, (s, s_)
    c = ['/\ a\n/\ b\n/\ c', 'd', 'e']
    s = cov._vertical_op(c)
    s_ = ' /\ /\ a\n    /\ b\n    /\ c\n /\ d\n /\ e'
    assert s == s_, (s, s_)
    c = ['/\ a\n/\ b\n/\ c', 'd', 'e']
    s = cov._vertical_op(c, op='or')
    s_ = ' \/ /\ a\n    /\ b\n    /\ c\n \/ d\n \/ e'
    assert s == s_, (s, s_)
    c = ['e']
    s = cov._vertical_op(c)
    s_ = c[0]
    assert s == s_, (s, s_)
    c = ['/\ a\n/\ b\n/\ c']
    s = cov._vertical_op(c)
    s_ = c[0]
    assert s == s_, (s, s_)
    c = ['a', 'b', 'c']
    s = cov._vertical_op(c, op='and', latex=True)
    c = [s, 'd', 'e']
    s = cov._vertical_op(c, op='or', latex=True)
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
    f = fol.add_expr('x = 1')
    care = fol.true
    s = (
        '(a_x = 2) /\ (2 <= b_x) /\ (b_x <= 3) '
        '/\ (a_y = 1 ) /\ (b_y = 5)')
    cover = fol.add_expr(s)
    r = cov._list_orthotope_expr(cover, px, fol)
    r = set(r)
    r_ = {'(x = 2) /\ (y \in 1 .. 5)',
          '(x \in 2 .. 3) /\ (y \in 1 .. 5)'}
    assert r == r_, (r, r_)
    # simple syntax, for parsing back
    # (needed until able to parse `x \in a .. b` expressions)
    r = cov._list_orthotope_expr(cover, px, fol, simple=True)
    r = set(r)
    r_ = {'(x = 2) /\ (1 <= y) /\ (y <= 5)',
          '(2 <= x) /\ (x <= 3) /\ (1 <= y) /\ (y <= 5)'}
    assert r == r_, (r, r_)
    # clipping on, but nothing to clip
    r = cov._list_orthotope_expr(cover, px, fol, use_dom=True)
    r = set(r)
    r_ = {'(x = 2) /\ (y \in 1 .. 5)',
          '(x \in 2 .. 3) /\ (y \in 1 .. 5)'}
    assert r == r_, (r, r_)
    # clip using type hints
    s = (
        '(a_x = -4) /\ (5 <= b_x)'
        '/\ (a_y = 1 ) /\ (b_y = 5)')
    cover = fol.add_expr(s)
    r = cov._list_orthotope_expr(cover, px, fol, use_dom=True)
    r = set(r)
    r_ = {'(y \in 1 .. 5)'}
    assert r == r_, (r, r_)
    # empty orthotopes
    s = (
        '(a_x = -4) /\ (5 <= b_x)'
        '/\ (a_y = 3 ) /\ (b_y = 1)')
    cover = fol.add_expr(s)
    with assert_raises(AssertionError):
        cov._list_orthotope_expr(cover, px, fol, use_dom=True)
    with assert_raises(AssertionError):
        cov._list_orthotope_expr(cover, px, fol)


def test_clip_subrange():
    ab = (6, 9)
    dom = (0, 10)
    r = cov._clip_subrange(ab, dom, 'x')
    assert r == ab, (r, ab)
    ab = (-5, 9)
    dom = (0, 10)
    r = cov._clip_subrange(ab, dom, 'x')
    r_ = (0, 9)
    assert r == r_, (r, r_)
    ab = (6, 15)
    dom = (0, 10)
    r = cov._clip_subrange(ab, dom, 'x')
    r_ = (6, 10)
    assert r == r_, (r, r_)


def test_check_type_hint():
    hint = dict(dom=(0, 50), width=6, signed=True)
    with assert_raises(AssertionError):
        cov._check_type_hint(10, 0, hint, 'x')
    cov._check_type_hint(2, 5, hint, 'y')


def test_care_implies_type_hints():
    fol = _fol.Context()
    fol.declare(x=(-4, 5), y=(-7, 15))
    f = fol.add_expr('0 < x  /\  x < 4')
    care = fol.add_expr('-2 <= y  /\  y <= 4')
    r = cov._care_implies_type_hints(f, care, fol)
    assert r is False, r
    care = fol.add_expr(
        '1 <= x  /\  x <= 6  /\ '
        '-2 <= y  /\  y <= 4')
    r = cov._care_implies_type_hints(f, care, fol)
    assert r is False, r
    care = fol.add_expr(
        '1 <= x  /\  x <= 5  /\ '
        '-2 <= y  /\  y <= 4')
    r = cov._care_implies_type_hints(f, care, fol)
    assert r is True, r


def test_f_implies_care():
    fol = _fol.Context()
    fol.declare(x=(-4, 5))
    f = fol.add_expr('0 < x  /\  x < 4')
    care = fol.add_expr('-2 <= x  /\  x <= 4')
    r = cov._f_implies_care(f, care, fol)
    assert r is True, r
    care = fol.add_expr('-2 <= x  /\  x <= 2')
    r = cov._f_implies_care(f, care, fol)
    assert r is False, r


def test_list_type_hints():
    with assert_raises(AssertionError):
        cov._list_type_hints(list(), 'whatever')
    table = dict(
        x=dict(type='int', dom=(-4, 5)),
        y=dict(type='int', dom=(-7, 15)))
    vrs = ['x', 'y']
    r = cov._list_type_hints(vrs, table)
    r_ = [r'x \in -4 .. 5',
          r'y \in -7 .. 15']
    assert r == r_, (r, r_)


def test_list_limits():
    table = dict(
        x=dict(type='int', dom=(-4, 5), width=4, signed=True),
        y=dict(type='int', dom=(-7, 15), width=5, signed=True))
    r = cov._list_limits(['x'], table)
    r_ = ['x \in -8 .. 7']
    assert r == r_, (r, r_)
    r = cov._list_limits(['x', 'y'], table)
    r_ = ['x \in -8 .. 7', 'y \in -16 .. 15']
    assert r == r_, (r, r_)


def test_bitfield_limits():
    hint = dict(width=1, signed=False)
    r = cov._bitfield_limits(hint)
    assert r == (0, 1), r
    hint = dict(width=2, signed=False)
    r = cov._bitfield_limits(hint)
    assert r == (0, 3), r
    hint = dict(width=10, signed=False)
    r = cov._bitfield_limits(hint)
    assert r == (0, 1023), r
    hint = dict(width=1, signed=True)
    r = cov._bitfield_limits(hint)
    assert r == (-1, 0), r
    hint = dict(width=2, signed=True)
    r = cov._bitfield_limits(hint)
    assert r == (-2, 1), r
    hint = dict(width=10, signed=True)
    r = cov._bitfield_limits(hint)
    assert r == (-512, 511), r


def test_conjoin_type_hints():
    fol = _fol.Context()
    fol.declare(x=(-4, 5), y=(-7, 15))
    vrs = ['x']
    u = cov._conjoin_type_hints(vrs, fol)
    u_ = fol.add_expr('-4 <= x  /\  x <= 5')
    assert u == u_, (u, u_)
    vrs = ['y']
    u = cov._conjoin_type_hints(vrs, fol)
    u_ = fol.add_expr('-7 <= y  /\  y <= 15')
    assert u == u_, (u, u_)
    vrs = ['x', 'y']
    u = cov._conjoin_type_hints(vrs, fol)
    u_ = fol.add_expr(
        '-4 <= x  /\  x <= 5 /\ '
        '-7 <= y  /\  y <= 15')
    assert u == u_, (u, u_)


def test_format_range():
    r = cov._format_range('wqd', 'g', 'k')
    r_ = 'wqd \in g .. k'
    assert r == r_, (r, r_)


def test_orthotopes_iter():
    fol = _fol.Context()
    fol.declare(p=(2, 9))
    # careful with the type hint
    u = fol.add_expr('(0 <= p) /\ (p <= 10)')
    c = list(cov._orthotopes_iter(u, fol))
    assert len(c) == 11, c


def test_setup_aux_vars():
    fol = _fol.Context()
    fol.declare(x=(-4, 5), y=(-7, 15))
    f = fol.add_expr('x = 2')
    care = fol.true
    vrs, px, qx, p_to_q = cov._setup_aux_vars(f, care, fol)
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
    t = cov._parameter_table(vrs, table, 'u', 'v')
    params = dict(u_x='x', v_x='x', u_y='y', v_y='y')
    for p, x in params.items():
        assert p in t, (p, t)
        dom = t[p]
        dom_ = table[x]['dom']
        assert dom == dom_, (dom, dom_)


def test_parameter_variables():
    x = ['x', 'y']
    px = cov._parameter_variables(x, 'a', 'b')
    px_ = dict(
        x=dict(a='a_x', b='b_x'),
        y=dict(a='a_y', b='b_y'))
    assert px == px_, (px, px_)


def test_map_parameters_to_vars():
    px, _ = dummy_parameters()
    d = cov._map_parameters_to_vars(px)
    d_ = dict(a_x='x', b_x='x',
              a_y='y', b_y='y')
    assert d == d_, (d, d_)


def test_collect_parameters():
    px, _ = dummy_parameters()
    c = cov._collect_parameters(px)
    c_ = {'a_x', 'b_x', 'a_y', 'b_y'}
    assert c == c_, (c, c_)


def test_parameter_varmap():
    px, qx = dummy_parameters()
    d = cov._parameter_varmap(px, qx)
    d_ = {('a_x', 'b_x'): ('u_x', 'v_x'),
          ('a_y', 'b_y'): ('u_y', 'v_y')}
    assert d == d_, (d, d_)


def test_renaming_between_parameters():
    px, qx = dummy_parameters()
    d = cov._renaming_between_parameters(px, qx)
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
    r = cov._replace_prime(pvar)
    assert r == "x_p", r
    with assert_raises(AssertionError):
         cov._replace_prime("a'bc")
    with assert_raises(AssertionError):
         cov._replace_prime("a'bc'")
    # identity
    var = "x"
    var_ = cov._replace_prime(var)
    assert var == var_, (var, var_)


def test_add_prime_like_too():
    table = dict(x=(-4, 5), y='bool')
    t = cov._add_prime_like_too(table)
    assert 'x' in t, t
    assert 'y' in t, t
    xp = cov._prime_like('x')
    yp = cov._prime_like('y')
    assert xp != 'x', xp
    assert yp != 'y', yp
    assert xp in t, (xp, t)
    assert yp in t, (yp, t)
    assert t['x'] == table['x'], t
    assert t['y'] == table['y'], t
    assert t[xp] == t['x'], t
    assert t[yp] == t['y'], t
    with assert_raises(AssertionError):
        table["x'"] = tuple(table['x'])
        cov._add_prime_like_too(table)


def test_prime_like():
    var = 'x'
    pvar = cov._prime_like(var)
    assert pvar != var, (pvar, var)
    assert pvar == 'x_cp', pvar


def test_branch_and_bound_class():
    fol = _fol.Context()
    fol.declare(p=(0, 3), q=(5, 7))
    p_leq_q = fol.add_expr('p <= q')
    p_to_q = {'p': 'q'}
    bab = cov._BranchAndBound(
        p_leq_q, None, None, None,
        p_to_q, None, None, fol)
    bab.lower_bound = 15
    with assert_raises(AssertionError):
        bab.upper_bound = 10
    bab.upper_bound = 20
    # only init for lower bound
    with assert_raises(AssertionError):
        bab.lower_bound = 17
    with assert_raises(AssertionError):
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
    print('{n} test functions'.format(n=n))
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
