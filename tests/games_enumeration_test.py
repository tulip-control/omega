"""Tests for `omega.games.enumeration`."""
import logging
logging.getLogger('omega').setLevel(logging.WARNING)

import networkx as nx

from omega.games import enumeration as enum
from omega.symbolic import fol as _fol
from omega.symbolic import temporal as symbolic


def test_action_to_steps():
    aut = symbolic.Automaton()
    aut.declare_variables(x='bool', y=(0, 17))
    env = 'env_foo'
    sys = 'sys_bar'
    aut.varlist[env] = ['x']
    aut.varlist[sys] = ['y']
    keys = ('x', 'y')
    aut.init[env] = aut.add_expr('x /\ (y = 1)')
    aut.init[sys] = aut.true
    aut.action[env] = aut.true
    aut.action[sys] = aut.add_expr("y' /= y")
    aut.win['<>[]'] = aut.bdds_from('x')
    aut.win['[]<>'] = aut.bdds_from('y != 1')
    aut.qinit = '\A \A'
    aut.moore = True
    aut.prime_varlists()
    g = enum.action_to_steps(
        aut, env=env, sys=sys, qinit=aut.qinit)
    # 36 states reachable, but should enumerate fewer
    assert len(g) == 4, g.nodes()
    # these are state projections (partial assignments)
    # a state assigns to all variable names
    # (infinitely many)
    states = {
        enum._node_tuple(d, keys)
        for u, d in g.nodes(data=True)}
    assert tuple([True, 1]) in states, states
    r = {p for p in states if p[0] is True}
    assert len(r) == 2
    r = {p for p in states if p[0] is False}
    assert len(r) == 2


def test_enumerate_state_machine():
    aut = symbolic.Automaton()
    aut.declare_variables(x='bool', y=(0, 17))
    init = aut.add_expr('x /\ (y = 1)')
    action = aut.add_expr('''
        /\ ( (x /\ (y = 1)) => (~ x' /\ (y' = 2)) )
        /\ ( (~ x /\ (y = 2)) => (x' /\ (y' = 1)) )
        ''')
    g = enum.enumerate_state_machine(init, action, aut)
    assert len(g) == 2, len(g)
    e = list(g.edges())
    assert len(e) == 2, len(e)


def test__primed_vars_per_quantifier():
    varlist = dict(env=['x'], sys=['y', 'z'])
    primed_vars = enum._primed_vars_per_quantifier(varlist)
    primed_vars_ = dict(env={"x'"}, sys={"y'", "z'"})
    assert primed_vars == primed_vars_, primed_vars


def test_init_search():
    aut = symbolic.Automaton()
    aut.declare_variables(x='bool')
    aut.varlist = dict(env=[], sys=['x'])
    aut.init['env'] = aut.true
    aut.init['sys'] = 'x'
    aut.build()
    g = nx.DiGraph()
    fol = _init_context(aut)
    umap = dict()
    keys = ['x']
    qinit = '\A \E'
    queue, visited = enum._init_search(
        g, aut, umap, keys, qinit)
    assert len(queue) == 1, queue


def test_forall_init():
    aut = symbolic.Automaton()
    aut.declare_variables(
        x=(3, 5), y='bool', z='bool')
    aut.varlist = dict(env=['x'], sys=['y', 'z'])
    # single initial state
    s = '(x = 4) /\ ~ y /\ z'
    aut.init['env'] = aut.add_expr(s)
    aut.init['sys'] = aut.true
    aut.build()
    g = nx.DiGraph()
    fol = _init_context(aut)
    umap = dict()
    keys = ('x', 'z', 'y')
    queue, visited = enum._forall_init(
        g, aut, umap, keys)
    assert len(queue) == 1, queue
    (q,) = queue
    assert q in g, (q, g)
    d = g.nodes[q]
    d_ = dict(x=4, y=False, z=True)
    assert d == d_, d
    # multiple initial states: should pick all
    s = (
        '(x \in 3..5) /\ (x < 5) '
        '/\ ~ z /\ (z <=> TRUE \/ z <=> FALSE)')
    aut.init['env'] = aut.add_expr(s)
    aut.build()
    g = nx.DiGraph()
    umap = dict()
    queue, visited = enum._forall_init(
        g, aut, umap, keys)
    assert len(queue) == 4, queue
    varnames = {'x', 'y', 'z'}
    for q in queue:
        assert q in g, (q, g)
        d = g.nodes[q]
        assert set(d) == varnames, d
        assert d['x'] < 5, d
        assert isinstance(d['y'], bool), d
        assert d['z'] is False, d


def test_exist_init():
    aut = symbolic.Automaton()
    aut.declare_variables(x=(0, 2), y='bool', z='bool')
    aut.varlist = dict(env={'x'}, sys={'y', 'z'})
    # single initial state
    aut.init['env'] = aut.true
    aut.init['sys'] = '(x = 1) /\ y /\ z'
    aut.build()
    g = nx.DiGraph()
    fol = _init_context(aut)
    umap = dict()
    keys = ('y', 'x', 'z')
    queue, visited = enum._exist_init(
        g, aut, umap, keys)
    assert len(queue) == 1, queue
    (q,) = queue
    assert q in g, (q, g)
    d = g.nodes[q]
    d_ = dict(x=1, y=True, z=True)
    assert d == d_, d
    # multiple initial states: should pick one
    s = '(x = 1) /\ y'
    aut.init['env'] = aut.add_expr(s)
    a = aut.build()
    g = nx.DiGraph()
    umap = dict()
    queue, visited = enum._exist_init(
        g, aut, umap, keys)
    assert len(queue) == 1, queue
    (q,) = queue
    assert q in g, (q, g)
    d = g.nodes[q]
    varnames = {'x', 'y', 'z'}
    assert set(d) == varnames, d
    assert d['x'] == 1, d
    assert d['y'] is True, d
    assert isinstance(d['z'], bool), d


def test_forall_exist_init():
    aut = symbolic.Automaton()
    aut.declare_variables(x='bool', y='bool')
    aut.varlist = dict(env={'x'}, sys={'y'})
    # single initial state
    aut.init['env'] = 'x'
    aut.init['sys'] = 'x /\ y'
    aut.build()
    g = nx.DiGraph()
    fol = _init_context(aut)
    umap = dict()
    keys = ('x', 'y')
    queue, visited = enum._forall_exist_init(
        g, aut, umap, keys)
    assert len(queue) == 1, queue
    (q,) = queue
    assert q in g, (q, g)
    d = g.nodes[q]
    d_ = dict(x=True, y=True)
    assert d ==d_, (d, d_)
    # multiple initial states
    aut.init['env'] = 'TRUE'
    aut.init['sys'] = 'x <=> y'
    aut.build()
    g = nx.DiGraph()
    umap = dict()
    queue, visited = enum._forall_exist_init(
        g, aut, umap, keys)
    assert len(queue) == 2, queue
    q0, q1 = queue
    assert q0 in g, (q0, g)
    assert q1 in g, (q1, g)
    d0 = g.nodes[q0]
    d1 = g.nodes[q1]
    varnames = set(keys)
    assert set(d0) == varnames, (d0, varnames)
    assert set(d1) == varnames, (d1, varnames)
    # \A \E:  for each `x`, pick some `y`
    assert d0['x'] == d0['y'], d0
    assert d1['x'] == d1['y'], d1
    assert d0['x'] != d1['x'], (d0, d1)
    v = {d0['x'], d1['x']}
    v_ = {False, True}
    assert v == v_, v


def test_exist_forall_init():
    aut = symbolic.Automaton()
    aut.declare_variables(x='bool', y='bool')
    aut.varlist = dict(env={'x'}, sys={'y'})
    # single initial state
    aut.init['env'] = 'x'
    aut.init['sys'] = ' ~ y'
    a = aut.build()
    g = nx.DiGraph()
    fol = _init_context(aut)
    umap = dict()
    keys = ('x', 'y')
    queue, visited = enum._exist_forall_init(
        g, aut, umap, keys)
    assert len(queue) == 1, queue
    (q,) = queue
    assert q in g, (q, g)
    d = g.nodes[q]
    d_ = dict(x=True, y=False)
    assert d == d_, (d, d_)
    # multiple initial states
    aut.init['env'] = 'TRUE'
    aut.init['sys'] = 'y'
    a = aut.build()
    g = nx.DiGraph()
    umap = dict()
    queue, visited = enum._exist_forall_init(
        g, aut, umap, keys)
    assert len(queue) == 2, queue
    q0, q1 = queue
    assert q0 in g, (q0, g)
    assert q1 in g, (q1, g)
    d0 = g.nodes[q0]
    d1 = g.nodes[q1]
    varnames = set(keys)
    assert set(d0) == varnames, (d0, varnames)
    assert set(d1) == varnames, (d1, varnames)
    # \E \A picks same `y` for all initial states
    assert d0['y'] is True, d0
    assert d1['y'] is True, d1
    v = {d0['x'], d1['x']}
    v_ = {False, True}
    assert v == v_, v


def test_find_node():
    u_ = 101
    d = dict(x=False, y=10)
    umap = {(False, 10): u_}
    keys = ('x', 'y')
    u = enum._find_node(d, umap, keys)
    assert u == u_, (u, u_)


def test_add_new_node():
    g = nx.DiGraph()
    queue = list()
    umap = dict()
    keys = ('x', 'y')
    d = dict(x=False, y=99)
    assert len(g) == 0, g
    u = enum._add_new_node(d, g, queue, umap, keys)
    assert u == 0, u
    assert len(g) == 1, g
    assert u in g, (u, g.nodes())
    du = g.nodes[u]
    assert du == d, du
    values = (False, 99)
    assert values in umap, (values, umap)
    v = umap[values]
    assert u == v, v


def test_add_to_visited():
    c = _fol.Context()
    c.declare(x='bool', y=(0, 10))
    bdd = c.bdd
    values = dict(x=True, y=5)
    visited = bdd.false
    new_visited = enum._add_to_visited(values, visited, c)
    s = 'x /\ (y = 5)'
    u = c.add_expr(s)
    assert new_visited == u


def test_node_tuple():
    d = dict(a=10, b='g', gandalf=True)
    keys = ('b', 'gandalf', 'a')
    r = enum._node_tuple(d, keys)
    r_ = ('g', True, 10)
    assert r == r_, r


def _init_context(aut):
    c = _fol.Context()
    c.add_vars(aut.vars)
    c.bdd = aut.bdd
    return c
