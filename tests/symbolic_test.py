import logging

import dd.bdd

from omega.automata import TransitionSystem
from omega.logic import bitvector as bv
from omega.symbolic import bdd as sym_bdd
from omega.symbolic import bdd_iterative as bdd_trs
from omega.symbolic import logicizer
from omega.symbolic import symbolic


log = logging.getLogger('astutils')
log.setLevel('ERROR')
log = logging.getLogger('omega')
log.setLevel('ERROR')


def test_symbolic_automaton():
    aut = symbolic.Automaton()
    aut.vars['x'] = dict(
        type='bool',
        owner='env')
    aut.vars['y'] = dict(
        type='int',
        dom=(3, 17),
        owner='sys')
    aut.init['env'].append('x')
    aut.action['env'].append("x -> ! x'")
    aut.init['sys'].append('y = 5')
    aut.action['sys'].append("(y < 6) -> (y' > 10)")
    # strategy definition
    assert aut.moore is True, aut.moore
    assert aut.plus_one is True, aut.plus_one
    assert aut.qinit == '\A \A', aut.qinit
    # str
    s = str(aut)
    assert s.startswith('Symbolic automaton:'), s[:10]
    assert s.endswith('> 10)\n'), s[-3:]
    # data persistence
    s = aut.dumps()
    d = eval(s)
    assert isinstance(d, dict), d
    keys = set(d)
    keys_ = {
        'vars', 'init', 'action', 'win',
        'acceptance', 'moore', 'plus_one', 'qinit'}
    assert keys == keys_, keys


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


def test_slugsin_parser():
    parser = sym_bdd.Parser()
    s = '! x'
    u = parser.parse(s)
    assert_is_operator(u, '!')
    (x,) = u.operands
    assert_is_var(x, 'x')
    s = '& x y'
    u = parser.parse(s)
    assert_is_operator(u, '&')
    x, y = u.operands
    assert_is_var(x, 'x')
    assert_is_var(y, 'y')
    s = '| x y'
    u = parser.parse(s)
    assert_is_operator(u, '|')
    x, y = u.operands
    assert_is_var(x, 'x')
    assert_is_var(y, 'y')
    s = '^ x12 y0'
    u = parser.parse(s)
    assert_is_operator(u, '^')
    x12, y0 = u.operands
    assert_is_var(x12, 'x12')
    assert_is_var(y0, 'y0')
    s = '$1 0'
    u = parser.parse(s)
    assert_is_buffer(u, 1)
    (a,) = u.memory
    assert_is_number(a, 0)
    s = '$2 0 1'
    u = parser.parse(s)
    assert_is_buffer(u, 2)
    a, b = u.memory
    assert_is_number(a, 0)
    assert_is_number(b, 1)
    s = '$2 $2 1 ?0 ?0'
    u = parser.parse(s)
    assert_is_buffer(u, 2)
    a, b = u.memory
    assert_is_register(b, 0)
    assert_is_buffer(a, 2)
    a, b = a.memory
    assert_is_number(a, 1)
    assert_is_register(b, 0)
    s = '\E x & x y'
    u = parser.parse(s)
    assert_is_operator(u, '\E')
    qvars, e = u.operands
    assert_is_var(qvars, 'x')
    assert_is_operator(e, '&')
    x, y = e.operands
    assert_is_var(x, 'x')
    assert_is_var(y, 'y')
    s = '\A y | y ! x4'
    u = parser.parse(s)
    assert_is_operator(u, '\A')
    qvars, e = u.operands
    assert_is_var(qvars, 'y')
    assert_is_operator(e, '|')
    y, not_x4 = e.operands
    assert_is_var(y, 'y')
    assert_is_operator(not_x4, '!')
    (x4,) = not_x4.operands
    assert_is_var(x4, 'x4')
    s = '\E x \A y | x y'
    u = parser.parse(s)
    assert_is_operator(u, '\E')
    qvars, e = u.operands
    assert_is_var(qvars, 'x')
    assert_is_operator(e, '\A')
    qvars, e = e.operands
    assert_is_var(qvars, 'y')
    assert_is_operator(e, '|')
    x, y = e.operands
    assert_is_var(x, 'x')
    assert_is_var(y, 'y')
    s = '\S $4 x y  z w  & y w'
    u = parser.parse(s)
    assert_is_operator(u, '\S')
    subs, e = u.operands
    assert_is_buffer(subs, 4)
    x, y, z, w = subs.memory
    assert_is_var(x, 'x')
    assert_is_var(y, 'y')
    assert_is_var(z, 'z')
    assert_is_var(w, 'w')
    assert_is_operator(e, '&')
    y, w = e.operands
    assert_is_var(y, 'y')
    assert_is_var(w, 'w')


def assert_is_operator(u, operator):
    assert hasattr(u, 'type'), u
    assert u.type == 'operator', u.type
    assert u.operator == operator


def assert_is_var(u, var):
    assert hasattr(u, 'type'), u
    assert u.type == 'var', u.type
    assert u.value == var, u.value


def assert_is_number(u, j):
    assert hasattr(u, 'type'), u
    assert u.type == 'num', u.type
    assert u.value == str(j), u.value


def assert_is_buffer(u, n):
    assert hasattr(u, 'type'), u
    assert u.type == 'buffer', u.type
    assert hasattr(u, 'memory'), u
    assert len(u.memory) == n, u.memory


def assert_is_register(u, idx):
    assert hasattr(u, 'type'), u
    assert u.type == 'register', u.type
    assert u.value == str(idx), u.value


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


def test_logicizer_env():
    g = TransitionSystem()
    g.vars['x'] = 'bool'
    g.owner = 'env'
    g.add_edge(0, 1, x=True)
    g.add_edge(1, 2, formula="x'")
    g.add_edge(2, 1)
    aut = logicizer.graph_to_logic(
        g,
        nodevar='k',
        ignore_initial=True,
        self_loops=True)
    assert 'x' in aut.vars, aut.vars
    assert 'k' in aut.vars, aut.vars
    xtype = aut.vars['x']['type']
    ktype = aut.vars['k']['type']
    assert xtype == 'bool', xtype
    assert ktype == 'saturating', ktype
    (s,) = aut.action['env']
    s_ = (
        "(((((k = 0)) -> (((x <-> True)) & ((k' = 1)))) \n"
        "& (((k = 1)) -> ((x') & ((k' = 2))))) \n"
        "& (((k = 2)) -> ((k' = 1)))) | (k' = k)")
    assert s == s_, s
