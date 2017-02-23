#!/usr/bin/env python
import logging
from dd import bdd as _bdd
import networkx as nx
from omega.logic import bitvector as bv
from omega.symbolic import bdd as bddizer
from nose import tools as nt


logger = logging.getLogger(__name__)
logging.getLogger('tulip.ltl_parser_log').setLevel(logging.WARNING)
h = logging.StreamHandler()
log = logging.getLogger('omega.logic.bitvector')
log.setLevel(logging.WARNING)
log.addHandler(h)
logging.getLogger('astutils').setLevel('ERROR')

# TODO: test truncation, test ALU up to 32 bits


def test_bitvector_name_conflicts():
    # no conflict
    t = {'x_1': dict(type='bool', owner='env'),
         'x': dict(type='int', dom=(0, 1), owner='sys',
                   signed=False, width=1)}
    bv._add_bitnames(t)
    assert 'bitnames' in t['x'], t
    assert t['x']['bitnames'] == ['x_0'], t
    # integer `x` mapped to `x_0`, conflict with Boolean `x_0`
    t['x_0'] = t.pop('x_1')
    with nt.assert_raises(AssertionError):
        bv._add_bitnames(t)


def test_bitfield_to_int_states():
    t = {'x': dict(type='bool'),
         'y': dict(type='int', signed=True, bitnames=['y0', 'y1', 'y2'])}
    g = nx.DiGraph()
    w = [dict(x=1, y0=1, y1=1, y2=0),
         dict(x=0, y0=0, y1=1, y2=1),
         dict(x=1, y0=1, y1=1, y2=1)]
    for i, d in enumerate(w):
        g.add_node(i, state=d)
    g.add_edges_from([(0, 1), (1, 2), (2, 1)])
    h = bv.bitfield_to_int_states(g, t)
    assert set(h) == {0, 1, 2}
    assert set(h.edges()) == {(0, 1), (1, 2), (2, 1)}
    z = [dict(x=1, y=3), dict(x=0, y=-2), dict(x=1, y=-1)]
    for u, d in h.nodes_iter(data=True):
        assert z[u] == d['state']


def test_bitfields_to_ints():
    t = {'x': dict(type='bool'),
         'y': dict(type='int', signed=True, bitnames=['y0', 'y1', 'y2'])}
    bit_state = {'x': 0, 'y0': 0, 'y1': 1, 'y2': 1}
    d = bv.bitfields_to_ints(bit_state, t)
    assert d == {'x': 0, 'y': -2}


t = {'a': {'type': 'int',
           'signed': True,
           'bitnames': ['a0', 'a1']},
     'b': {'type': 'int',
           'signed': True,
           'bitnames': ['b0', 'b1']},
     'x': {'type': 'int',
           'signed': True,
           'bitnames': ['x@0.0.3', 'x@1']},
     'y': {'type': 'int',
           'signed': True,
           'bitnames': ['y0', 'y1', 'y2']},
     'q': {'type': 'bool'},
     'r': {'type': 'bool'}}
parser = bv._parser


def test_flatten_comparator():
    """Test arithmetic predicates."""
    # tree = parser.parse('x + 1 <= 2')
    # print(repr(tree) + '\n')
    log.setLevel(logging.ERROR)
    # (in)equality
    assert parser.parse('a = 1').flatten(t=t) == '$ 1 ! | ^ a0 1 | ^ a1 0 0'
    assert parser.parse('a != 1').flatten(t=t) == '$ 1 | ^ a0 1 | ^ a1 0 0'
    # '<' comparator
    f = parser.parse('a < 1').flatten(t=t)
    # print(f)
    assert (f == ('$ 7 '
                  '^ ^ a0 ! 1 1 '
                  '| & a0 ! 1 & ^ a0 ! 1 1 '
                  '^ ^ a1 ! 0 ? 1 '
                  '| & a1 ! 0 & ^ a1 ! 0 ? 1 '
                  '^ ^ a1 ! 0 ? 3 '
                  '| & a1 ! 0 & ^ a1 ! 0 ? 3 '
                  '^ ! ^ a1 0 ? 5')), f
    # TODO: more bits, larger numbers


def test_flatten_arithmetic():
    """Test arithmetic functions."""
    # addition
    mem = list()
    res = parser.parse('a + 1').flatten(t=t, mem=mem)
    assert res == ['? 0', '? 2', '? 4'], res
    assert mem == ['^ ^ a0 1 0',
                   '| & a0 1 & ^ a0 1 0',
                   '^ ^ a1 0 ? 1',
                   '| & a1 0 & ^ a1 0 ? 1',
                   '^ ^ a1 0 ? 3',
                   '| & a1 0 & ^ a1 0 ? 3'], mem
    # TODO: subtraction


def test_flatten_quantifiers():
    # single qvar
    s = '\A a: True'
    r = parser.parse(s).flatten(t=t)
    assert r == ' \A & a0 a1 1', r
    s = '\E y: False'
    r = parser.parse(s).flatten(t=t)
    assert r == ' \E & & y0 y1 y2 0', r
    s = '\E y: x = y'
    r = parser.parse(s).flatten(t=t)
    eq = parser.parse('x = y').flatten(t=t)
    r_ = ' \E & & y0 y1 y2 {eq}'.format(eq=eq)
    assert r == r_, (r, r_)
    # multiple qvars
    s = '\E a, b: True'
    r = parser.parse(s).flatten(t=t)
    assert r == ' \E & & & a0 a1 b0 b1 1', r
    s = '\E a, x: x - a > 0'
    r = parser.parse(s).flatten(t=t)
    h = parser.parse('x - a > 0').flatten(t=t)
    r_ = ' \E & & & a0 a1 x@0.0.3 x@1 {h}'.format(h=h)
    assert r == r_, (r, r_)
    s = '\A r: r | ! q'
    r = parser.parse(s).flatten(t=t)
    h = parser.parse('r | ! q').flatten(t=t)
    r_ = ' \A r {h}'.format(h=h)
    assert r == r_, (r, r_)


def test_flatten_substitution():
    # single pair
    s = '\S a / b: True'
    r = parser.parse(s).flatten(t=t)
    assert r == ' \S $4 a0 b0 a1 b1 1', r
    s = '\S q / r: False'
    r = parser.parse(s).flatten(t=t)
    assert r == ' \S $2 q r 0', r
    s = '\S b / x: x - y <= 0'
    r = parser.parse(s).flatten(t=t)
    h = parser.parse('x - y <= 0').flatten(t=t)
    r_ = ' \S $4 b0 x@0.0.3 b1 x@1 {h}'.format(h=h)
    assert r == r_, r
    # multiple pairs
    s = '\S a / b,  q / r:  False'
    r = parser.parse(s).flatten(t=t)
    r_ = ' \S $6 a0 b0 a1 b1 q r 0'
    assert r == r_, r
    # swap: order of substitutions should be preserved
    s = '\S q / r, a / b:  False'
    r = parser.parse(s).flatten(t=t)
    r_ = ' \S $6 q r a0 b0 a1 b1 0'
    assert r == r_, r
    # more complex expr
    s = '\S a / b, q / r:  r | ! (a != b)'
    r = parser.parse(s).flatten(t=t)
    h = parser.parse('r | ! (a != b)').flatten(t=t)
    r_ = ' \S $6 a0 b0 a1 b1 q r {h}'.format(h=h)
    assert r == r_, r
    # invalid input
    c = [
        '\S a / q: True',
        '\S q / a: True',
        '\S a / y: True']
    for s in c:
        print(s)
        with nt.assert_raises(AssertionError):
            u = parser.parse(s)
            u.flatten(t=t)


def test_div_mul_expr():
    mem = list()
    res = parser.parse('4 / 2').flatten(t=t, mem=mem)
    r = _evaluate_result(res, mem)
    assert r == 2, r
    mem = list()
    res = parser.parse('-8 / 3').flatten(t=t, mem=mem)
    r = _evaluate_result(res, mem)
    assert r == -2, r
    mem = list()
    res = parser.parse('4 * 2').flatten(t=t, mem=mem)
    r = _evaluate_result(res, mem)
    assert r == 8, r
    mem = list()
    res = parser.parse('4 % 3').flatten(t=t, mem=mem)
    r = _evaluate_result(res, mem)
    assert r == 1, r
    mem = list()
    res = parser.parse('4 % -3').flatten(t=t, mem=mem)
    r = _evaluate_result(res, mem)
    assert r == 1, r


def test_division():
    # 1 / 1 = 1 * 1 + 0
    x = ['1', '0']
    y = ['1', '0']
    _divide(x, y, q=1, r=0)
    # -2 / 1 = -2 * 1 + 0
    x = ['0', '1']
    y = ['1', '0']
    _divide(x, y, q=-2, r=0)
    # 0 / 1 == 0 * 1 + 0
    x = ['0', '0']
    y = ['1', '0']
    _divide(x, y, q=0, r=0)
    # 2 / -2 = -1 * (-2) + 0
    x = ['0', '1', '0']
    y = ['0', '1', '1']
    _divide(x, y, q=-1, r=0)
    #
    # negative numbers
    # -4 / 2 = -2 * 2 + 0
    x = ['0', '0', '1']
    y = ['0', '1', '0']
    _divide(x, y, q=-2, r=0)
    # 4 / -2 = -2 * (-2) + 0
    x = ['0', '0', '1', '0']
    y = ['0', '1']
    _divide(x, y, q=-2, r=0)
    #
    # C99 semantics
    # 4 / -3 = -1 * (-3) + 1
    x = ['0', '0', '1', '0']
    y = ['1', '0', '1']
    _divide(x, y, q=-1, r=1)
    # -4 / 3 = -1 * 3 - 1
    x = ['0', '0', '1', '1']
    y = ['1', '1', '0']
    _divide(x, y, q=-1, r=-1)
    #
    # divisor > dividend
    # 4 / 5 = 0 * 5 + 4
    x = ['0', '0', '1', '0']
    y = ['1', '0', '1', '0']
    _divide(x, y, q=0, r=4)
    # -4 / -5 = 0 * (-5) -4
    x = ['0', '0', '1', '1']
    y = ['1', '1', '0', '1']
    _divide(x, y, q=0, r=-4)


def _divide(x, y, q, r):
    quo, rem, mem = bv.restoring_divider(x, y)
    q_ = _evaluate_result(quo, mem)
    r_ = _evaluate_result(rem, mem)
    assert q_ == q, (q_, r_)
    assert r_ == r, (q_, r_)


def test_multiplier():
    # LSB ... MSB
    # 0 * 0 = 0
    x = ['0', '0']
    y = list(x)
    res, mem = bv.multiplier(x, y, start=0)
    r = _evaluate_result(res, mem)
    assert r == 0, r
    # 1 * 0 = 0
    x = ['0', '0']
    y = ['1', '0']
    res, mem = bv.multiplier(x, y, start=0)
    r = _evaluate_result(res, mem)
    assert r == 0, r
    # -1 * 1 = -1
    x = ['1', '1']
    y = ['1', '0']
    res, mem = bv.multiplier(x, y, start=0)
    r = _evaluate_result(res, mem)
    # 1 * -1 = -1
    x = ['1', '0']
    y = ['1', '1']
    res, mem = bv.multiplier(x, y, start=0)
    r = _evaluate_result(res, mem)
    assert r == -1, r
    # -2 * 2 = -4
    x = ['0', '1', '1']
    y = ['0', '1', '0']
    res, mem = bv.multiplier(x, y, start=0)
    r = _evaluate_result(res, mem)
    assert r == -4, r
    # 8 * 8 = 64
    x = ['0', '0', '0', '1', '0']
    y = list(x)
    res, mem = bv.multiplier(x, y, start=0)
    r = _evaluate_result(res, mem)
    assert r == 64, r
    # -16 * 5 = -80
    x = ['0', '0', '0', '0', '1', '1']
    y = ['1', '0', '1', '0']
    res, mem = bv.multiplier(x, y, start=0)
    r = _evaluate_result(res, mem)
    assert r == -80, r


def _evaluate_result(result, memory):
    """Return integer, given a result and memory w/o variables.

    @type result: `list`
    @type memory: `list`
    """
    bdd = _bdd.BDD({'x': 0})
    n = len(memory) + 1
    mem = ' '.join(memory)
    bits = list()
    for bit in result:
        s = '$ {n} {mem} {bit}'.format(n=n, mem=mem, bit=bit)
        u = bddizer.add_expr(s, bdd)
        bits.append(u)
    bits = [b == 1 for b in bits]
    # print([int(b) for b in bits])
    j = bv.twos_complement_to_int(bits)
    return j


def test_fixed_shift():
    # 0 is LSB
    x = ['0', '1', '0']
    c = 1
    r = bv.fixed_shift(x, c, left=True, logical=None)
    assert r == ['0', '0', '1'], r
    c = 2
    r = bv.fixed_shift(x, c, left=True, logical=None)
    assert r == ['0', '0', '0'], r
    c = 1
    r = bv.fixed_shift(x, c, left=False, logical=False)
    assert r == ['1', '0', '0'], r
    x = ['0', '1', '1']
    # unsigned
    r = bv.fixed_shift(x, c, left=False, logical=True)
    assert r == ['1', '1', '0']
    # signed
    r = bv.fixed_shift(x, c, left=False, logical=False)
    assert r == ['1', '1', '1']


def test_barrel_shifter():
    x = ['x0', 'x1', 'x2', 'x3']
    y = ['y0', 'y1']
    m = ['& ! y0 x0',
         '| & ! y0 x1 & y0 x0',
         '| & ! y0 x2 & y0 x1',
         '| & ! y0 x3 & y0 x2',
         '& ! y1 ? 0',
         '& ! y1 ? 1',
         '| & ! y1 ? 2 & y1 ? 0',
         '| & ! y1 ? 3 & y1 ? 1']
    # stage -1
    z, mem = bv.barrel_shifter(x, y, -1)
    assert z == x
    assert mem == list()
    # stage 0
    z, mem = bv.barrel_shifter(x, y, 0)
    assert z == ['? 0', '? 1', '? 2', '? 3']
    assert len(mem) == 4
    assert mem == m[:4]
    # stage 1
    z, mem = bv.barrel_shifter(x, y, 1)
    print(z)
    print(bv._format_mem(mem))
    assert z == ['? 4', '? 5', '? 6', '? 7']
    assert len(mem) == 8
    assert mem == m
    # fun: (2**n)-bit x
    # n = 5
    # x = ['x{i}'.format(i=i) for i in xrange(2**n)]
    # y = ['y{i}'.format(i=i) for i in xrange(n)]
    # z, mem = sl.barrel_shifter(x, y)
    # print(z)
    # print(sl._format_mem(mem))


def test_truncate():
    x = list('01010100011')
    n = 4
    r = bv.truncate(x, n)
    assert len(r) == n
    assert r == list('0101')


def test_twos_complement_for_var():
    t = dict(
        x=dict(type='bool'),
        y=dict(type='int', dom=(-2, 1), signed=True,
               bitnames=['y0', 'y1']),
        z=dict(type='int', dom=(0, 1), signed=False,
               bitnames=['z0']),
        w=dict(type='int', dom=(-1, 0), signed=False,
               bitnames=['w0']))
    with nt.assert_raises(Exception):
        bv.var_to_twos_complement('r', t)
    with nt.assert_raises(TypeError):
        bv.var_to_twos_complement('x', t)
    y = bv.var_to_twos_complement('y', t)
    assert y == ['y0', 'y1'], y
    z = bv.var_to_twos_complement('z', t)
    assert z == ['z0', '0'], z
    w = bv.var_to_twos_complement('w', t)
    assert w == ['w0', '1'], w


def test_twos_complement_for_int():
    f = bv.twos_complement_to_int
    g = bv.int_to_twos_complement
    pairs = {0: ['0', '0'],
             1: ['1', '0'],
             2: ['0', '1', '0'],
             5: ['1', '0', '1', '0'],
             -1: ['1', '1'],
             -2: ['0', '1', '1'],
             -3: ['1', '0', '1']}
    for k, v in pairs.items():
        assert g(k) == v
        assert k == f(v)
    pairs = {-1: ['1', '1', '1'],
             -2: ['0', '1', '1', '1'],
             2: ['0', '1', '0', '0']}
    for k, v in pairs.items():
        assert k == f(v)


def test_abs():
    x = ['1', '0']
    r, mem = bv.abs_(x)
    a = _evaluate_result(r, mem)
    assert a == 1, a
    x = ['0', '1']
    r, mem = bv.abs_(x)
    a = _evaluate_result(r, mem)
    assert a == 2, a
    x = ['1', '1']
    r, mem = bv.abs_(x)
    a = _evaluate_result(r, mem)
    assert a == 1, a


def test_equalize_width():
    x = list('0101')
    y = list('10')
    p, q = bv.equalize_width(x, y)
    assert len(p) == len(q) == 4
    for a in p[len(x):]:
        assert a == x[-1]
    for a in q[len(y):]:
        assert a == y[-1]


def test_sign_extension():
    t = {'a': {'type': 'int',
               'signed': True,
               'bitnames': ['a0', 'a1']},
         'b': {'type': 'int',
               'signed': True,
               'bitnames': ['b0', 'b1']}}
    with nt.assert_raises(ValueError):
        bv.sign_extension(['1'], 2)
    with nt.assert_raises(ValueError):
        bv.sign_extension(['1', '1'], 0)
    assert bv.sign_extension(['1', '1'], 3) == ['1', '1', '1']
    assert bv.sign_extension(['1', '0'], 3) == ['1', '0', '0']
    with nt.assert_raises(AssertionError):
        mem = list()
        parser.parse('a + 1').flatten(t=t)
    with nt.assert_raises(AssertionError):
        parser.parse('b < -1').flatten(t=t, mem=mem)


def test_ite():
    # ite connective
    x = 'x'
    y = 'y'
    z = 'z'
    s = bv.ite_connective(x, y, z)
    r = '$ 2 x | & y ? 0 & z ! ? 0'
    assert s == r, s
    # ite connective flattening
    t = {'x': {'type': 'bool'},
         'y': {'type': 'bool'},
         'z': {'type': 'bool'}}
    p = parser.parse('ite( x, y, z)')
    s = p.flatten(t=t)
    assert s == r, s
    with nt.assert_raises(AssertionError):
        bv.ite_connective('a', ['b', 'c'], 'd')
    # ite function
    x = 'x'
    y = ['y0', 'y1']
    z = ['z0', 'z1']
    r, mem = bv.ite_function(x, y, z, start=0)
    correct = [
        'x',
        '| & y0 ? 0 & z0 ! ? 0',
        '| & y1 ? 0 & z1 ! ? 0']
    assert mem == correct, mem
    assert r == ['? 1', '? 2']
    # flip
    r, more_mem = bv.ite_function(x, z, y, start=len(mem))
    mem.extend(more_mem)
    correct.extend([
        'x',
        '| & z0 ? 3 & y0 ! ? 3',
        '| & z1 ? 3 & y1 ! ? 3'])
    assert mem == correct, mem
    assert r == ['? 4', '? 5']
    # ite function flattening
    t = {'x': {'type': 'bool'},
         'y': {'type': 'int',
               'signed': True,
               'bitnames': ['a0', 'a1']},
         'z': {'type': 'int',
               'signed': True,
               'bitnames': ['b0', 'b1']}}
    mem = list()
    r = p.flatten(t=t, mem=mem)
    assert mem == [
        'x',
        '| & a0 ? 0 & b0 ! ? 0',
        '| & a1 ? 0 & b1 ! ? 0']
    assert r == ['? 1', '? 2']
    # b, c of different length
    with nt.assert_raises(AssertionError):
        bv.ite_function('x', ['y0'], ['z0', 'z1', 'z2'], start=0)


def test_init_to_logic():
    # bool
    d = dict(type='bool', init='False')
    c = bv._init_to_logic('x', d)
    assert c == 'x <=> False', c
    # number
    d = dict(type='other', init=5)
    c = bv._init_to_logic('y', d)
    assert c == 'y = 5', c
    # TODO: create equivalent test
    # array
    # d = dict(dom='numerical', length=3, init=init)
    # c = logic.init_to_logic('x', d)
    # assert c == ['x0 = 5', 'x1 = 5', 'x2 = 5'], c


def test_bool_eq_number():
    t = dict(x=dict(type='bool', owner='env'))
    # wrong
    s = 'x <=> 0'
    tree = parser.parse(s)
    with nt.assert_raises(AssertionError):
        tree.flatten(t=t)
    # correct
    s = 'x <=> false'
    tree = parser.parse(s)
    r = tree.flatten(t=t)
    assert r == ' ! ^ x 0 ', r


def test_mixed_fol_bitblasted():
    t = dict(x=dict(type='bool', owner='sys'),
             y=dict(type='int', dom=(0, 3), owner='sys'))
    t = bv.bitblast_table(t)
    s = '(x /\ y_0) \/ (y < 0)'
    tree_0 = parser.parse(s)
    q = 'y < 0'
    tree_1 = parser.parse(q)
    f0 = tree_0.flatten(t=t)
    f1 = tree_1.flatten(t=t)
    assert f0 == ' |  & x y_0  {f1} '.format(f1=f1), (f0, f1)


def test_type_invariants():
    t = dict(x=dict(type='int', dom=(0, 3), init=2))
    t = bv.bitblast_table(t)
    init, action = bv.type_invariants(t)
    init_ = dict(x=['x = 2', '(0 <= x)  /\  (x <= 3)'])
    assert init == init_, init
    s = (
         "    (0 <= x)  /\  (x <= 3)"
         "  /\ (0 <= x') /\  (x' <= 3)")
    action_ = dict(x=[s])
    assert action == action_, action


def test_prefix_parser():
    parser = bddizer.Parser()
    nodes = parser.nodes
    # &, !
    e = '& x ! y'
    t = parser.parse(e)
    assert isinstance(t, nodes.Operator), t
    assert t.operator == '&', t.operator
    assert len(t.operands) == 2, t.operands
    a, b = t.operands
    assert isinstance(a, nodes.Var), a
    assert a.value == 'x', a.value
    assert isinstance(b, nodes.Operator), b
    assert b.operator == '!', b.operator
    assert len(b.operands) == 1, b.operands
    (y,) = b.operands
    assert isinstance(y, nodes.Var), y
    assert y.value == 'y', y
    # memory buffer: $
    e = '&   $ 1 ! x  y'
    t = parser.parse(e)
    # &
    assert isinstance(t, nodes.Operator)
    assert t.operator == '&', t.operator
    assert len(t.operands) == 2, t.operands
    a, b = t.operands
    assert isinstance(a, nodes.Buffer), a
    assert len(a.memory) == 1, a.memory
    # ! x
    (notx,) = a.memory
    assert isinstance(notx, nodes.Operator), notx
    assert len(notx.operands) == 1, notx.operands
    # x
    (x,) = notx.operands
    assert isinstance(x, nodes.Var), x
    assert x.value == 'x', x.value
    # y
    assert isinstance(b, nodes.Var), b
    assert b.value == 'y', b.value
    # register: ?
    e = '$ 2   x    & y  ? 0'
    t = parser.parse(e)
    assert isinstance(t, nodes.Buffer), t
    assert len(t.memory) == 2, t.memory
    x, c = t.memory
    # x
    assert isinstance(x, nodes.Var), x
    assert x.value == 'x', x.value
    # &
    assert isinstance(c, nodes.Operator), c
    assert c.operator == '&', c.operator
    assert len(c.operands) == 2, c.operands
    y, reg = c.operands
    assert isinstance(y, nodes.Var), y
    assert y.value == 'y', y.value
    assert isinstance(reg, nodes.Register), reg
    assert reg.value == '0', reg.value


def test_flatten_memory_nodes():
    # buffer
    nodes = bddizer.DebugNodes()
    x = nodes.Var('x')
    mem = [x, x, x]
    b = nodes.Buffer(mem)
    assert b.memory is mem, b.memory
    f = b.flatten()
    assert f == '\nbuffer[3](\n x,\n x,\n x)', f
    # register
    reg = nodes.Register('1')
    f = reg.flatten()
    assert f == 'reg[1]', f


def test_make_table():
    d = dict(x=(0, 2), y='bool', w='bool', z=(-2, 5))
    env_vars = {'x', 'y'}
    t = bv.make_table(d, env_vars)
    t_ = dict(
        x=dict(type='saturating', owner='env', dom=(0, 2)),
        y=dict(type='bool', owner='env', dom=None),
        z=dict(type='saturating', owner='sys', dom=(-2, 5)),
        w=dict(type='bool', owner='sys', dom=None))
    assert t == t_, (t, t_)


if __name__ == '__main__':
    test_type_invariants()
