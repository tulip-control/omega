"""Tests for `omega.logic.lexyacc."""
from omega.logic import lexyacc


parser = lexyacc.Parser()


def test_quantifiers():
    s = '\E x: True'
    t = parser.parse(s)
    assert hasattr(t, 'operator'), t
    assert t.type == 'operator', t
    assert t.operator == '\E', t.operator
    assert len(t.operands) == 2, t.operands
    qvars, e = t.operands
    assert len(qvars) == 1, qvars
    (x,) = qvars
    _assert_is_var_node(x, 'x')
    assert hasattr(e, 'type'), e
    assert e.type == 'bool', e.type
    assert e.value == 'True', e.value
    s = '\E x, y: False'
    t = parser.parse(s)
    assert hasattr(t, 'type'), t
    assert t.type == 'operator', t.type
    assert t.operator == '\E', t.operator
    assert len(t.operands) == 2, t.operands
    qvars, e = t.operands
    assert len(qvars) == 2, qvars
    x, y = qvars
    _assert_is_var_node(x, 'x')
    _assert_is_var_node(y, 'y')
    assert hasattr(e, 'type'), e
    assert e.type == 'bool', e.type
    assert e.value == 'False', e.value
    s = '\A y: True'
    t = parser.parse(s)
    assert t.operator == '\A', t.operator
    s = '\A x, y, z: (x \/ ~ y) /\ z'
    t = parser.parse(s)
    assert t.operator == '\A', t.operator
    assert len(t.operands) == 2, t.operands
    qvars, e = t.operands
    assert len(qvars) == 3, qvars
    r = e.flatten()
    r_ = '( ( x \/ ( ~ y ) ) /\ z )'
    assert r == r_, (r, r_)


def test_substitution():
    s = '\S a / b: True'
    t = parser.parse(s)
    assert hasattr(t, 'type'), t
    assert t.type == 'operator', t.type
    assert t.operator == '\S', t.operator
    assert len(t.operands) == 2, t.operands
    pairs, e = t.operands
    assert len(pairs) == 1, pairs
    (ab,) = pairs
    a, b = ab
    _assert_is_var_node(a, 'a')
    _assert_is_var_node(b, 'b')
    assert hasattr(e, 'type'), e
    assert e.type == 'bool', e.type
    assert e.value == 'True', e.value
    s = '\S a / b,  c / d: False'
    t = parser.parse(s)
    assert hasattr(t, 'type'), t
    assert t.type == 'operator', t
    assert t.operator == '\S', t.operator
    assert len(t.operands) == 2, t.operands
    pairs, e = t.operands
    assert len(pairs) == 2, pairs
    ab, cd = pairs
    assert len(ab) == 2, ab
    a, b = ab
    _assert_is_var_node(a, 'a')
    _assert_is_var_node(b, 'b')
    c, d = cd
    _assert_is_var_node(c, 'c')
    _assert_is_var_node(d, 'd')
    assert hasattr(e, 'type')
    assert e.type == 'bool', e.type
    assert e.value == 'False', e.value


def test_range():
    s = r'z \in 0 .. 2'
    r = parser.parse(s).flatten()
    r_ = r'( z \in ( 0 .. 2 ) )'
    assert r == r_, r
    s = r'''
           z \in 0 .. 2
        /\ y \in -45 .. 1
        '''
    r = parser.parse(s).flatten()
    r_ = (
        '( ( z \in ( 0 .. 2 ) )'
        ' /\ ( y \in ( -45 .. 1 ) ) )')
    assert r == r_, r


def _assert_is_var_node(x, var):
    assert hasattr(x, 'type'), x
    assert x.type == 'var', x.type
    assert x.value == var, x.value


if __name__ == '__main__':
    test_range()
