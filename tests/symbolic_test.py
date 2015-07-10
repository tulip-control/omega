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
    d, prime, partition = symbolic._partition_vars(v, uv)
    order = {"a": 0, "a'": 1, "b": 2, "b'": 3, "c": 4, "c'": 5}
    prime_ = {k: k + "'" for k in v}
    partition_ = dict(
        uvars={"a"},
        upvars={"a'"},
        evars={"b", "c"},
        epvars={"b'", "c'"})
    assert d == order, d
    assert prime == prime_, (prime, prime_)
    assert partition == partition_, (partition, partition_)


def test_bdd_nodes():
    parser = sym_bdd.parser
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


def slugsin_parser(s, t):
    """Helper that converts prefix to infix syntax for readability."""
    slugs_table = t.to_slugs()
    ltl_parser = bv.Parser()
    p = ltl_parser.parse(s)
    bv.add_bitnames(slugs_table)
    s = p.flatten(t=slugs_table)
    slugsin_parser = sym_bdd.Parser()
    print(slugsin_parser.parse(s))
