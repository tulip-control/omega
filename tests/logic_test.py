"""Tests for `omega.logic`."""
from nose.tools import assert_raises
from omega.logic import past


parser = past.Parser()


def test_flatten_previous_var():
    testers = dict()
    context = 'boolean'
    x = past.Nodes.Var('x')
    s = past._flatten_previous('--X', x, testers, context)
    assert s == 'x_prev1', s
    # tester
    assert 'x_prev1' in testers, testers
    d = testers['x_prev1']
    assert isinstance(d, dict), d
    # init
    a = d.get('init')
    b = '(! x_prev1)'
    assert a == b, a
    # trans
    a = d.get('trans')
    b = '((X x_prev1) <-> x)'
    assert a == b, a


def test_flatten_previous_boolean():
    testers = dict()
    context = 'boolean'
    x = past.Nodes.Var('x')
    y = past.Nodes.Var('y')
    previous_x = past.Nodes.Unary('--X', x)
    e = past.Nodes.Binary('&', previous_x, y)
    s = e.flatten(testers, context=context)
    assert s == '( x_prev1 & y )', s
    # tester
    assert 'x_prev1' in testers, testers
    d = testers['x_prev1']
    assert isinstance(d, dict), d
    # init
    a = d.get('init')
    b = '(! x_prev1)'
    assert a == b, a
    # trans
    a = d.get('trans')
    b = '((X x_prev1) <-> x)'
    assert a == b, a


def test_flatten_previous_arithmetic():
    testers = dict()
    context = 'arithmetic'
    x = past.Nodes.Var('x')
    y = past.Nodes.Var('y')
    previous_x = past.Nodes.Unary('-X', x)
    e = past.Nodes.Arithmetic('+', previous_x, y)
    s = e.flatten(testers=testers, context=context)
    assert s == '( x_prev1 + y )', s
    # tester
    assert 'x_prev1' in testers
    d = testers['x_prev1']
    assert isinstance(d, dict), d
    # init
    a = d.get('init')
    b = 'True'
    assert a == b, a
    # trans
    a = d.get('trans')
    b = '((X x_prev1) = x)'
    assert a == b, a


def test_flatten_previous_boolean_expr():
    testers = dict()
    context = 'boolean'
    # "-X (x & y)"
    x = past.Nodes.Var('x')
    y = past.Nodes.Var('y')
    conj = past.Nodes.Binary('&', x, y)
    e = past.Nodes.Unary('--X', conj)
    s = e.flatten(testers=testers, context=context)
    assert s == '_aux0', s
    # tester
    assert '_aux0' in testers, testers
    d = testers['_aux0']
    assert isinstance(d, dict), d
    # init
    a = d.get('init')
    b = '(! _aux0)'
    assert a == b, a
    # trans
    a = d.get('trans')
    b = '((X _aux0) <-> ( x & y ))'
    assert a == b, a


def test_flatten_previous_arithmetic_expr():
    testers = dict()
    context = 'arithmetic'
    # "-X (z + 3)"
    z = past.Nodes.Var('z')
    n = past.Nodes.Num('3')
    plus = past.Nodes.Arithmetic('+', z, n)
    e = past.Nodes.Unary('-X', plus)
    s = e.flatten(testers=testers, context=context)
    assert s == '( z_prev1 + 3 )', s
    # tester
    assert 'z_prev1' in testers, testers
    d = testers['z_prev1']
    assert isinstance(d, dict), d
    # init
    a = d.get('init')
    b = 'True'
    assert a == b, a
    # trans
    a = d.get('trans')
    b = '((X z_prev1) = z)'
    assert a == b, a


def test_flatten_nested_previous():
    testers = dict()
    context = 'boolean'
    # "-X (q & -X (3 = -X (p + 3)))"
    p = past.Nodes.Var('p')
    q = past.Nodes.Var('q')
    n = past.Nodes.Num('3')
    plus = past.Nodes.Arithmetic('+', p, n)
    prev_plus = past.Nodes.Unary('-X', plus)
    eq = past.Nodes.Comparator('=', n, prev_plus)
    prev_eq = past.Nodes.Unary('--X', eq)
    conj = past.Nodes.Binary('&', q, prev_eq)
    e = past.Nodes.Unary('-X', conj)
    s = e.flatten(testers=testers, context=context)
    assert s == '_aux2', s
    #
    # tester for "-X p" (p_prev1)
    #
    assert 'p_prev1' in testers, testers
    d = testers['p_prev1']
    assert isinstance(d, dict), d
    # init
    a = d.get('init')
    b = 'True'
    assert a == b, a
    # trans
    a = d.get('trans')
    b = '((X p_prev1) = p)'
    assert a == b, a
    #
    # tester for "-X (p + 3 = 3)" (_aux1)
    #
    assert '_aux1' in testers, testers
    d = testers['_aux1']
    assert isinstance(d, dict), d
    # init
    a = d.get('init')
    b = '(! _aux1)'
    assert a == b, a
    # trans
    a = d.get('trans')
    b = '((X _aux1) <-> ( 3 = ( p_prev1 + 3 ) ))'
    assert a == b, a
    #
    # tester for whole formula (_aux1)
    #
    assert '_aux2' in testers, testers
    d = testers['_aux2']
    assert isinstance(d, dict), d
    # init
    a = d.get('init')
    b = '_aux2'
    assert a == b, a
    # trans
    a = d.get('trans')
    b = '((X _aux2) <-> ( q & _aux1 ))'
    assert a == b, a


def test_flatten_since():
    testers = dict()
    context = 'boolean'
    p = past.Nodes.Var('p')
    q = past.Nodes.Var('q')
    since = past.Nodes.Binary('S', p, q)
    s = since.flatten(testers=testers, context=context)
    assert s == '_aux0', s
    # tester
    assert '_aux0' in testers
    d = testers['_aux0']
    assert isinstance(d, dict), d
    # init
    a = d.get('init')
    b = '(_aux0 <-> q)'
    assert a == b, a
    # trans
    a = d.get('trans')
    b = '((X _aux0) <-> ((X q) | ((X p) & _aux0)))'
    assert a == b, a


def test_past_parser_boolean():
    t = dict(a=dict(type='bool', owner='sys'),
             b=dict(type='bool', owner='env'))
    s = 'a. & b'
    dvars, init, trans = past.translate(s, t)
    r = 'a_prev1'
    assert init == r, init
    r = '(( a_prev1 & b )) & (((X a_prev1) <-> a))'
    assert trans == r, trans


def test_parser_strong_weak_previous():
    # strong previous
    tree = parser.parse('--X p')
    assert len(tree) == 2, tree
    assert hasattr(tree, 'operator'), tree
    op = tree.operator
    assert op == '--X', op
    assert hasattr(tree, 'operands'), tree
    c = tree.operands
    assert len(c) == 1, c
    (p,) = c
    assert hasattr(p, 'value'), p
    v = p.value
    assert v == 'p', v
    # weak previous
    tree = parser.parse('-X p')
    assert len(tree) == 2, tree
    assert hasattr(tree, 'operator'), tree
    op = tree.operator
    assert op == '-X', op
    assert hasattr(tree, 'operands'), tree
    c = tree.operands
    assert len(c) == 1, c
    (p,) = c
    assert hasattr(p, 'value'), p
    v = p.value
    assert v == 'p', v


def test_parser_nested():
    t = dict(
        a=dict(type='bool', owner='sys'),
        p=dict(type='int', dom=(0, 2), owner='env'),
        q=dict(type='int', dom=(0, 5), owner='sys'))
    s = '(--X a & ((p. + q). = 5))'
    dvars, init, trans = past.translate(s, t, debug=True)
    assert init == '(! a_prev1)', init
    r = (
        '(( a_prev1 & ( ( p_prev2 + q_prev1 ) = 5 ) )) & '
        '(((((X a_prev1) <-> a)) & '
        '(((X p_prev2) = p))) & (((X q_prev1) = q)))')
    assert trans == r, trans


def test_parser_multi_previous():
    s = 'a..'
    tree = parser.parse(s)
    testers = dict()
    r = tree.flatten(testers=testers, context='boolean')
    assert r == 'a_prev2', r
    assert len(testers) == 1, testers


def test_context_checks():
    # boolean
    s = 'x + y'
    tree = parser.parse(s)
    tree.flatten(testers=dict, context='arithmetic')
    with assert_raises(AssertionError):
        tree.flatten(testers=dict, context='boolean')
    # arithmetic
    s = 'p & q'
    tree = parser.parse(s)
    tree.flatten(testers=dict, context='boolean')
    with assert_raises(AssertionError):
        tree.flatten(testers=dict, context='arithmetic')
    # nested
    s = 'a & (b + 3)'
    tree = parser.parse(s)
    with assert_raises(AssertionError):
        tree.flatten(testers=dict, context='boolean')


if __name__ == '__main__':
    test_context_checks()
