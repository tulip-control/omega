#!/usr/bin/env python
"""Test `omega.symbolic.fol`."""
from nose import tools as nt

from omega.symbolic import fol as _fol


def test_add_vars():
    # Boolean-valued variable
    fol = _fol.Context()
    bdd = fol.bdd
    d = dict(x=dict(type='bool'))
    fol.add_vars(d)
    assert 'x' in fol.vars, fol.vars
    dx = fol.vars['x']
    assert 'type' in dx, dx
    type_x = dx['type']
    assert type_x == 'bool', type_x
    assert 'x' in bdd.vars
    assert 'x_0' not in bdd.vars
    # integer-valued variable
    fol = _fol.Context()
    bdd = fol.bdd
    d = dict(y=dict(type='int', dom=(0, 2)))
    fol.add_vars(d)
    assert 'y' in fol.vars, fol.vars
    dy = fol.vars['y']
    assert 'type' in dy, dy
    type_dy = dy['type']
    assert type_dy == 'int', type_dy
    # regression regarding bit naming convention
    assert 'y_0' in bdd.vars
    assert 'y_1' in bdd.vars
    assert 'y_2' not in bdd.vars
    assert 'y' not in bdd.vars
    # primed vars
    fol = _fol.Context()
    bdd = fol.bdd
    d = {"y'": dict(type='int', dom=(0, 1))}
    fol.add_vars(d)
    assert "y'" in fol.vars, fol.vars
    assert "y_0'" in bdd.vars, bdd.vars
    assert "y'_0" not in bdd.vars, bdd.vars
    # adding same vars twice
    fol = _fol.Context()
    d = dict(x=dict(type='bool'))
    fol.add_vars(d)
    fol.add_vars(d)
    # mismatch with existing var
    d = dict(x=dict(type='int'))
    with nt.assert_raises(AssertionError):
        fol.add_vars(d)
    # mixed new and existing
    d = dict(x=dict(type='bool'),
             y=dict(type='int', dom=(0, 5)))
    fol.add_vars(d)
    d['y']['dom'] = (3, 15)
    with nt.assert_raises(AssertionError):
        fol.add_vars(d)


def test_support():
    fol = _fol.Context()
    bdd = fol.bdd
    s = 'True'
    u = fol.add_expr(s)
    r = fol.support(u)
    assert r == set(), r
    # single variable
    d = dict(x=dict(type='int', dom=(0, 10)),
             y=dict(type='bool'))
    fol.add_vars(d)
    with nt.assert_raises(AssertionError):
        u = fol.add_expr('x')
    with nt.assert_raises(AssertionError):
        u = fol.add_expr(5)
    s = 'x = 1'
    u = fol.add_expr(s)
    r = fol.support(u)
    assert r == {'x'}, r
    s = '(x < 2) | ! y'
    u = fol.add_expr(s)
    r = fol.support(u)
    assert r == {'x', 'y'}, r
    del u


def test_replace():
    fol = _fol.Context()
    fol.add_vars(dict(
        x=dict(type='int', dom=(0, 12)),
        y=dict(type='int', dom=(0, 12)),
        z=dict(type='int', dom=(0, 3)),
        w=dict(type='bool')))
    # with vars
    u = fol.add_expr('x = 1')
    subs = {'x': 'y'}
    u = fol.replace(u, subs)
    u_ = fol.add_expr('y = 1')
    assert u == u_, (u, u_)
    u = fol.add_expr('x = 1')
    # with mismatched substitutions
    subs = {'x': 'z'}
    with nt.assert_raises(AssertionError):
        fol.replace(u, subs)
    subs = {'x': 'w'}
    with nt.assert_raises(AssertionError):
        fol.replace(u, subs)
    # with constants
    # Boolean
    u = fol.add_expr('w')
    subs = {'w': True}
    u = fol.replace(u, subs)
    assert u == fol.bdd.true
    u = fol.add_expr('w')
    subs = {'w': False}
    u = fol.replace(u, subs)
    assert u == fol.bdd.false
    # integer
    u = fol.add_expr('z = 2')
    subs = {'z': 2}
    u = fol.replace(u, subs)
    assert u == fol.bdd.true
    u = fol.add_expr('z = 2')
    subs = {'z': 3}
    u = fol.replace(u, subs)
    assert u == fol.bdd.false
    # outside coarse type bound
    u = fol.add_expr('z = 2')
    subs = {'z': 4}
    with nt.assert_raises(AssertionError):
        fol.replace(u, subs)
    # no effect
    u = fol.add_expr('w')
    subs = {'z': True}
    v = fol.replace(u, subs)
    assert u == v
    del u, u_, v


# requires `dd.cudd`
def replace_with_bdd():
    fol = _fol.Context()
    fol.add_vars(dict(
        x=dict(type='bool'),
        y=dict(type='bool')))
    u = fol.add_expr('x => y')
    subs = {'x': fol.bdd.true}
    u = fol.replace_with_bdd(u, subs)
    u_ = fol.add_expr('y')
    assert u == u_, (u, u_)
    del u, u_, subs


def test_quantifiers():
    """Test syntax for rigid quantification."""
    fol = _fol.Context()
    bdd = fol.bdd
    d = dict(x=dict(type='int', dom=(0, 5), owner='sys'))
    fol.add_vars(d)
    # no `qvars`
    u = fol.add_expr('True')
    r = fol.exist(set(), u)
    assert r == u, (r, u)
    u = fol.add_expr('False')
    r = fol.exist(set(), u)
    assert r == u, (r, u)
    u = fol.add_expr('x = 5')
    r = fol.exist(set(), u)
    assert r == u, (r, u)
    # TYPENESS !!!
    s = '\E x: (x = 7)'
    u = fol.add_expr(s)
    assert u == bdd.true
    u = fol.add_expr('x = 3')
    u = fol.forall(['x'], u)
    assert u == bdd.false
    # fine-grained type hint ignored
    u = fol.add_expr('x <= 5')
    u = fol.forall(['x'], u)
    assert u == bdd.false
    # coarse type-hint `(-1 + 2**a)..(-1 + 2**b)` effective
    u = fol.add_expr('x < 8')
    u = fol.forall(['x'], u)
    assert u == bdd.true
    # \E
    u = fol.add_expr('x = 2')
    u = fol.exist(['x'], u)
    assert u == bdd.true
    u = fol.add_expr('x < 0')
    u = fol.exist(['x'], u)
    assert u == bdd.false
    u = fol.add_expr('x > 5')
    u = fol.exist(['x'], u)
    assert u == bdd.true
    u = fol.add_expr('(6 <= x) & (x < 8)')
    u = fol.exist(['x'], u)
    assert u == bdd.true
    u = fol.add_expr('x > 7')
    u = fol.exist(['x'], u)
    assert u == bdd.false
    del u, r


def test_pick():
    fol = _fol.Context()
    fol.add_vars(dict(
        x=dict(type='bool'),
        y=dict(type='int', dom=(0, 2))))
    u = fol.add_expr('x')
    p = fol.pick(u, full=True, care_vars=['x'])
    for i in xrange(10):
        q = fol.pick(u, full=True, care_vars=['x'])
        assert p == q, (p, q)
    u = fol.add_expr('False')
    p = fol.pick(u, full=True, care_vars=['x'])
    assert p is None, p
    del u


def test_pick_iter():
    fol = _fol.Context()
    fol.add_vars(dict(
        x=dict(type='bool'),
        y=dict(type='int', dom=(0, 2))))
    u = fol.add_expr('True')
    gen = fol.pick_iter(u, full=True, care_vars=['x'])
    r = list(gen)
    assert len(r) == 2, r
    u = fol.add_expr('False')
    gen = fol.pick_iter(u, full=True, care_vars=['x'])
    r = list(gen)
    assert len(r) == 0, r
    u = fol.add_expr('x')
    gen = fol.pick_iter(u, full=True, care_vars=['x'])
    r = list(gen)
    assert len(r) == 1, r
    u = fol.add_expr('x')
    gen = fol.pick_iter(u, full=True, care_vars=['x', 'y'])
    r = list(gen)
    assert len(r) == 4, r
    del u


def test_add_expr():
    fol = _fol.Context()
    bdd = fol.bdd
    u = fol.add_expr('False')
    assert u == bdd.false, bdd.to_expr(u)
    d = dict(x=dict(type='int', dom=(0, 100)),
             y=dict(type='int', dom=(5, 23)))
    fol.add_vars(d)
    u = fol.add_expr('x < y + 5')
    v = fol.add_expr('x - 5 < y')
    assert u == v, (u, v)
    del u, v


def test_apply():
    fol = _fol.Context()
    bdd = fol.bdd
    d = dict(x=dict(type='bool'))
    fol.add_vars(d)
    u = fol.add_expr('x')
    v = fol.add_expr('! x')
    w = fol.apply('and', u, v)
    assert w == bdd.false
    w = fol.apply('or', u, v)
    assert w == bdd.true
    del u, v, w


def test_reorder():
    fol = _fol.Context()
    bdd = fol.bdd
    d = dict(x=dict(type='int', dom=(0, 7)),
             y=dict(type='int', dom=(0, 3)))
    fol.add_vars(d)
    top_bit = bdd.var_at_level(0)
    if top_bit.startswith('x'):
        var = 'y'
    elif top_bit.startswith('y'):
        var = 'x'
    else:
        raise AssertionError(str(top_bit))
    shift_vars = {var: dict(level=0)}
    _fol.reorder(shift_vars, fol)
    bit_0 = bdd.var_at_level(0)
    bit_1 = bdd.var_at_level(1)
    assert bit_0.startswith(var), bit_0
    assert bit_1.startswith(var), bit_1


if __name__ == '__main__':
    test_quantifiers()
