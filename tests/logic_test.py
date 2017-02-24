"""Tests for `omega.logic`."""
from nose.tools import assert_raises

from omega.logic import past
from omega.logic import syntax as stx


parser = past.parser


def test_flatten_previous_var():
    testers = dict()
    context = 'bool'
    x = past.Nodes.Var('x')
    s = past._flatten_previous(
        '--X', x, testers, context)
    assert s == 'x_prev1', s
    # tester
    assert 'x_prev1' in testers, testers
    d = testers['x_prev1']
    assert isinstance(d, dict), d
    # init
    a = d.get('init')
    b = '(~ x_prev1)'
    assert a == b, a
    # trans
    a = d.get('trans')
    b = '((X x_prev1) <=> x)'
    assert a == b, a


def test_flatten_previous_boolean():
    testers = dict()
    context = 'bool'
    x = past.Nodes.Var('x')
    y = past.Nodes.Var('y')
    previous_x = past.Nodes.Unary('--X', x)
    e = past.Nodes.Binary('/\\', previous_x, y)
    s = e.flatten(
        testers,
        context=context)
    assert s == '( x_prev1 /\ y )', s
    # tester
    assert 'x_prev1' in testers, testers
    d = testers['x_prev1']
    assert isinstance(d, dict), d
    # init
    a = d.get('init')
    b = '(~ x_prev1)'
    assert a == b, a
    # trans
    a = d.get('trans')
    b = '((X x_prev1) <=> x)'
    assert a == b, a


def test_flatten_previous_boolean_expr():
    testers = dict()
    context = 'bool'
    # "-X (x & y)"
    x = past.Nodes.Var('x')
    y = past.Nodes.Var('y')
    conj = past.Nodes.Binary('/\\', x, y)
    e = past.Nodes.Unary('--X', conj)
    s = e.flatten(
        testers=testers,
        context=context)
    assert s == '_aux0', s
    # tester
    assert '_aux0' in testers, testers
    d = testers['_aux0']
    assert isinstance(d, dict), d
    # init
    a = d.get('init')
    b = '(~ _aux0)'
    assert a == b, a
    # trans
    a = d.get('trans')
    b = '((X _aux0) <=> ( x /\ y ))'
    assert a == b, a


def test_flatten_nested_previous():
    testers = dict()
    context = 'bool'
    # "-X (q & -X (3 = (p + 3)))"
    p = past.Nodes.Var('p')
    q = past.Nodes.Var('q')
    n = past.Nodes.Num('3')
    plus = past.Nodes.Arithmetic('+', p, n)
    eq = past.Nodes.Comparator('=', n, plus)
    prev_eq = past.Nodes.Unary('--X', eq)
    conj = past.Nodes.Binary('/\\', q, prev_eq)
    e = past.Nodes.Unary('-X', conj)
    s = e.flatten(
        testers=testers,
        context=context)
    assert s == '_aux1', s
    #
    # tester for "-X (p + 3 = 3)" (_aux1)
    #
    assert '_aux1' in testers, testers
    d = testers['_aux1']
    assert isinstance(d, dict), d
    # init
    a = d.get('init')
    b = '_aux1'
    assert a == b, a
    # trans
    a = d.get('trans')
    b = '((X _aux1) <=> ( q /\ _aux0 ))'
    assert a == b, a
    #
    # tester for whole formula (_aux1)
    #
    assert '_aux1' in testers, testers
    d = testers['_aux1']
    assert isinstance(d, dict), d
    # init
    a = d.get('init')
    b = '_aux1'
    assert a == b, a
    # trans
    a = d.get('trans')
    b = '((X _aux1) <=> ( q /\ _aux0 ))'
    assert a == b, a


def test_flatten_since():
    testers = dict()
    context = 'bool'
    p = past.Nodes.Var('p')
    q = past.Nodes.Var('q')
    since = past.Nodes.Binary('S', p, q)
    s = since.flatten(
        testers=testers,
        context=context)
    assert s == '_aux0', s
    # tester
    assert '_aux0' in testers
    d = testers['_aux0']
    assert isinstance(d, dict), d
    # init
    a = d.get('init')
    b = '(_aux0 <=> q)'
    assert a == b, a
    # trans
    a = d.get('trans')
    b = '((X _aux0) <=> (    (X q) \/ ((X p) /\ _aux0)))'
    assert a == b, a


def test_past_parser_boolean():
    s = '-X a /\ b'
    dvars, r, init, trans, win = past.translate(s)
    init_ = 'a_prev1'
    assert init == init_, init
    r_ = '( a_prev1 /\ b )'
    assert r == r_, r
    trans_ = '((X a_prev1) <=> a)'
    assert trans == trans_, trans


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


def test_parser_mixed():
    s = '(--X a /\ ((p + q) = 5))'
    dvars, r, init, trans, win = past.translate(
        s, debug=True)
    assert init == '(~ a_prev1)', init
    r_ = '( a_prev1 /\ ( ( p + q ) = 5 ) )'
    assert r == r_, r


def test_parser_multi_previous():
    s = '--X --X a'
    tree = parser.parse(s)
    testers = dict()
    r = tree.flatten(testers=testers,
                     context='bool')
    assert r == '_aux1', r
    assert len(testers) == 2, testers


def test_context_checks():
    # boolean
    s = 'x + y'
    tree = parser.parse(s)
    tree.flatten(testers=dict,
                 context='arithmetic')
    with assert_raises(AssertionError):
        tree.flatten(testers=dict,
                     context='bool')
    # arithmetic
    s = 'x & y'
    tree = parser.parse(s)
    tree.flatten(testers=dict,
                 context='bool')
    with assert_raises(AssertionError):
        tree.flatten(testers=dict,
                     context='arithmetic')
    # nested
    s = 'y & (y + 3)'
    tree = parser.parse(s)
    with assert_raises(AssertionError):
        tree.flatten(testers=dict,
                     context='bool')


def test_isinstance_str():
    s = 's'
    r = stx.isinstance_str(s)
    assert r is True, r
    s = 0
    r = stx.isinstance_str(s)
    assert r is False, r


if __name__ == '__main__':
    test_context_checks()
