"""Test `omega.symbolic.enumeration."""
import logging

import networkx as nx

from omega.symbolic import enumeration as enum
from omega.symbolic import symbolic


logging.getLogger('astutils').setLevel('ERROR')
logging.getLogger('omega').setLevel('ERROR')


def test_relation_to_graph():
    a = symbolic.Automaton()
    a.vars['x'] = dict(type='int', dom=(0, 5), owner='sys')
    a.vars['y'] = dict(type='bool', owner='sys')
    aut = a.build()
    u = aut.add_expr("(x = 4) & y & (x' = 0)")
    care_bits = aut.bdd.vars
    g = enum.relation_to_graph(
        u, aut, care_bits=care_bits)
    assert len(g) == 3, g.nodes()
    keys = ('x', 'y')
    r = {tuple(d[k] for k in keys)
         for k, d in g.nodes_iter(data=True)}
    r_ = {(4, True), (0, False), (0, True)}
    assert r == r_, r


def test_enumerate_int():
    b = [0, 0, 0]
    k = _enum_int(b)
    assert k == 0, k
    b = [0, 1, 0, 0]
    k = _enum_int(b)
    assert k == 2, k
    b = [1, 0, 1, 0]
    k = _enum_int(b)
    assert k == 5, k
    b = [0, 1, 0, 1]
    k = _enum_int(b)
    assert k == -6, k
    # partial assignment
    b = [0, 1, None, 0]
    r = set(enum._enumerate_int(b))
    assert r == {2, 6}, r
    b = [None, 1, None, 0]
    r = set(enum._enumerate_int(b))
    assert r == {2, 3, 6, 7}, r


def _enum_int(b):
    gen = enum._enumerate_int(b)
    (k,) = list(gen)
    return k


def test_product_iter():
    sets = dict(x={1, 2}, y={3, 4})
    model = dict(z=True)
    r = list(enum._take_product_iter(sets, model))
    r_ = [dict(x=1, y=3, z=True),
          dict(x=2, y=3, z=True),
          dict(x=1, y=4, z=True),
          dict(x=2, y=4, z=True)]
    for d in r:
        assert d in r_, d
    for d in r_:
        assert d in r, d
    # trivial case
    sets = dict()
    r = list(enum._take_product_iter(sets, model))
    assert r == [model], r


def test_unprime_any_primed():
    model = {"x'": 5, "y": False, "w'": 6}
    r = enum._unprime_any_primed(model)
    r_ = dict(x=5, y=False, w=6)
    assert r == r_, r


def test_find_or_add_model():
    model = dict(x=5, y=False)
    umap = dict()
    keys = ('x', 'y')
    u = enum._find_or_add_model(model, umap, keys)
    k = (5, False)
    assert k in umap, umap
    u_ = umap[k]
    assert u == u_, (u, u_)


def test_format_nx():
    g = nx.DiGraph()
    sorted_vars = ['x', 'y', 'w']
    g.add_node(0, x=5, y=3)
    g.add_node(1, w=True)
    g.add_edge(1, 0)
    h, umap = enum._format_nx(g, sorted_vars)
    assert len(h) == len(g), (h.nodes(), g.nodes())
    assert len(h) == len(umap), (h.nodes(), umap)
    ux = r' (x=5) &and; (y=3) \l'
    uy = r' (w=True) \l'
    assert h.has_edge(uy, ux), h.edges()


def test_square_conj():
    # single line
    c = ['a', 'b']
    s = enum._square_conj(c, 2, op='/\\')
    s_ = r' (a) /\ (b) \l'
    assert s == s_, s
    # multi-line conjunction
    c = ['a', 'b', 'c']
    s = enum._square_conj(c, 3, op='/\\')
    s_ = r'/\ (a) /\ (b) \l/\ (c) '
    assert s == s_, s
