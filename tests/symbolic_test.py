import logging
import dd.bdd
from omega.logic import bitvector as bv
from omega.symbolic import bdd as sym_bdd
from omega.symbolic import bdd_iterative as bdd_trs
from omega.symbolic import symbolic


log = logging.getLogger('astutils')
log.setLevel('ERROR')
log = logging.getLogger('omega')
log.setLevel('ERROR')


def test_partition_vars():
    bits = ['a', 'b', 'c']
    ubits = ['a']
    ebits = ['b', 'c']
    order = symbolic._add_primed_bits(bits)
    order_ = ["a", "a'", "b", "b'", "c", "c'"]
    assert order == order_, (order, order_)
    prime, partition = symbolic._partition_vars(bits, ubits, ebits)
    prime_ = {k: k + "'" for k in bits}
    partition_ = dict(
        uvars={"a"},
        upvars={"a'"},
        evars={"b", "c"},
        epvars={"b'", "c'"})
    assert prime == prime_, (prime, prime_)
    assert partition == partition_, (partition, partition_)


def test_iterative_bddizer():
    add = bdd_trs.add_expr
    order = {'x': 0, 'y': 1, 'z': 2}
    # x & y
    bdd = dd.bdd.BDD(order)
    e = '& x y'
    u = add(e, bdd)
    v = bdd.add_expr('x & y')
    assert u == v, (u, v)
    # buffers
    # (x & y) | ! z
    bdd = dd.bdd.BDD(order)
    e = '$ 3   & x y   ! z  | ? 0 ? 1'
    u = add(e, bdd)
    v = bdd.add_expr('(x & y) | ! z')
    assert u == v, (u, v)


def test_bddizer_propositional():
    add = sym_bdd.add_expr
    order = {'x': 0, 'y': 1, 'z': 2}
    # x & y
    bdd = dd.bdd.BDD(order)
    e = '& x y'
    u = add(e, bdd)
    v = bdd.add_expr('x & y')
    assert u == v, (u, v)
    # buffers
    # (x & y) | ! z
    bdd = dd.bdd.BDD(order)
    e = '$ 3   & x y   ! z  | ? 0 ? 1'
    u = add(e, bdd)
    v = bdd.add_expr('(x & y) | ! z')
    assert u == v, (u, v)
    #
    e = '& $2 & 1 x ?0 $3 | !x y z & ?1 z'
    s = 'x & z'
    u = add(e, bdd)
    v = bdd.add_expr(s)
    assert u == v, (u, v)


def test_bddizer_quantifiers():
    add = sym_bdd.add_expr
    order = {'x': 0, 'y': 1, 'z': 2}
    bdd = dd.bdd.BDD(order)
    e = '\E x 1'
    u = add(e, bdd)
    assert u == bdd.true, u
    e = '\E x 0'
    u = add(e, bdd)
    assert u == bdd.false, u
    e = '\A x 1'
    u = add(e, bdd)
    assert u == bdd.true, u
    e = '\A x 0'
    u = add(e, bdd)
    assert u == bdd.false, u
    e = '\A x x'
    u = add(e, bdd)
    assert u == bdd.false, u
    e = '\E x x'
    u = add(e, bdd)
    assert u == bdd.true, u
    e = '\A & x y y'
    u = add(e, bdd)
    assert u == bdd.false, u
    e = '\A x y'
    u = add(e, bdd)
    u_ = bdd.var('y')
    assert u == u_, (u, u_)
    e = '\E & x y & y x'
    u = add(e, bdd)
    assert u == bdd.true, u


def test_bddizer_substitution():
    add = sym_bdd.add_expr
    order = {'x': 0, 'y': 1, 'z': 2, 'w': 3}
    bdd = dd.bdd.BDD(order)
    e = '\S $2 x y y'
    u = add(e, bdd)
    u_ = bdd.var('x')
    assert u == u_, (u, u_)
    e = '\S $4 x y  z w  | y ! w'
    u = add(e, bdd)
    u_ = bdd.add_expr('x | ! z')
    assert u == u_, (u, u_)
    e = '$2 0 \S $2 x y y'
    u = add(e, bdd)
    u_ = bdd.var('x')
    assert u == u_, (u, u_)


def slugsin_parser(s, t):
    """Helper that converts prefix to infix syntax for readability."""
    slugs_table = t.to_slugs()
    ltl_parser = bv.Parser()
    p = ltl_parser.parse(s)
    bv.add_bitnames(slugs_table)
    s = p.flatten(t=slugs_table)
    slugsin_parser = sym_bdd.Parser()
    print(slugsin_parser.parse(s))
