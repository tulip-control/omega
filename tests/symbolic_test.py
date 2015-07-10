import logging
import dd.bdd
from omega.logic import bitvector as bv
from omega.symbolic import bdd as sym_bdd
from omega.symbolic import symbolic


log = logging.getLogger('astutils')
log.setLevel('ERROR')
log = logging.getLogger('omega')
log.setLevel('ERROR')


def test_partition_vars():
    v = ['a', 'b', 'c']
    uv = ['a']
    d, u2p, uvars, upvars, evars, epvars = symbolic._partition_vars(v, uv)
    order = {'a': 0, "a'": 1, 'b': 2, "b'": 3, 'c': 4, "c'": 5}
    assert d == order, d
    assert u2p == {0: 1, 2: 3, 4: 5}, u2p
    assert uvars == {0}, uvars
    assert upvars == {1}, upvars
    assert evars == {2, 4}, evars
    assert epvars == {3, 5}, epvars


def slugsin_parser(s, t):
    """Helper that converts prefix to infix syntax for readability."""
    slugs_table = t.to_slugs()
    ltl_parser = bv.Parser()
    p = ltl_parser.parse(s)
    bv.add_bitnames(slugs_table)
    s = p.flatten(t=slugs_table)
    slugsin_parser = _bdd.PrefixParser()
    print(slugsin_parser.parse(s))


def test_bdd_nodes():
    parser = PrefixParser()
    parser._ast = make_bdd_nodes()
    order = {'x': 0, 'y': 1, 'z': 2}
    # x & y
    bdd = dd.bdd.BDD(order)
    e = '& x y'
    t = parser.parse(e)
    u = t.flatten(bdd=bdd)
    v = bdd.add_expr('x & y')
    assert u == v, (u, v)
    # buffers
    # (x & y) | ! z
    bdd = dd.bdd.BDD(order)
    e = '$ 3   & x y   ! z  | ? 0 ? 1'
    t = parser.parse(e)
    u = t.flatten(bdd=bdd)
    v = bdd.add_expr('(x & y) | ! z')
    assert u == v, (u, v)
