#!/usr/bin/env python
"""Test `omega.symbolic.fol`."""
import logging
import pprint

from nose import tools as nt
from omega.symbolic import fol as _fol


log = logging.getLogger('dd')
log.setLevel(logging.WARNING)
log = logging.getLogger('omega.logic')
log.setLevel(logging.WARNING)


def test_declare():
    # Boolean-valued variable
    fol = _fol.Context()
    bdd = fol.bdd
    fol.declare(x='bool')
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
    fol.declare(y=(0, 2))
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
    d = {"y'": (0, 1)}
    fol.declare(**d)
    assert "y'" in fol.vars, fol.vars
    assert "y_0'" in bdd.vars, bdd.vars
    assert "y'_0" not in bdd.vars, bdd.vars
    # adding same vars twice
    fol = _fol.Context()
    fol.declare(x='bool')
    fol.declare(x='bool')
    # mismatch with existing var
    with nt.assert_raises(ValueError):
        fol.declare(x=(1, 5))
    # mixed new and existing
    fol.declare(x='bool', y=(0, 5))
    with nt.assert_raises(ValueError):
        fol.declare(x='bool', y=(3, 15))


def test_support():
    fol = _fol.Context()
    bdd = fol.bdd
    s = 'True'
    u = fol.add_expr(s)
    r = fol.support(u)
    assert r == set(), r
    # single variable
    fol.declare(x=(0, 10), y='bool')
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


def test_replace():
    fol = _fol.Context()
    fol.declare(
        x=(0, 12), y=(0, 12),
        z=(0, 3), w='bool')
    # with vars
    u = fol.add_expr('x = 1')
    subs = {'x': 'y'}
    u = fol.let(subs, u)
    u_ = fol.add_expr('y = 1')
    assert u == u_, (u, u_)
    u = fol.add_expr('x = 1')
    # with mismatched substitutions
    subs = {'x': 'z'}
    with nt.assert_raises(AssertionError):
        fol.let(subs, u)
    subs = {'x': 'w'}
    with nt.assert_raises(AssertionError):
        fol.let(subs, u)
    # with constants
    # Boolean
    u = fol.add_expr('w')
    subs = {'w': True}
    u = fol.let(subs, u)
    assert u == fol.bdd.true
    u = fol.add_expr('w')
    subs = {'w': False}
    u = fol.let(subs, u)
    assert u == fol.bdd.false
    # integer
    u = fol.add_expr('z = 2')
    subs = {'z': 2}
    u = fol.let(subs, u)
    assert u == fol.bdd.true
    u = fol.add_expr('z = 2')
    subs = {'z': 3}
    u = fol.let(subs, u)
    assert u == fol.bdd.false
    # outside coarse type bound
    u = fol.add_expr('z = 2')
    subs = {'z': 4}
    with nt.assert_raises(AssertionError):
        fol.let(subs, u)
    # no effect
    u = fol.add_expr('w')
    subs = {'z': True}
    v = fol.let(subs, u)
    assert u == v


# requires `dd.cudd`
def replace_with_bdd():
    fol = _fol.Context()
    fol.declare(x='bool', y='bool')
    u = fol.add_expr('x => y')
    subs = {'x': fol.bdd.true}
    u = fol.replace_with_bdd(u, subs)
    u_ = fol.add_expr('y')
    assert u == u_, (u, u_)


def test_quantifiers():
    """Test syntax for rigid quantification."""
    fol = _fol.Context()
    bdd = fol.bdd
    fol.declare(x=(0, 5))
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


def test_pick():
    fol = _fol.Context()
    fol.declare(x='bool', y=(0, 2))
    u = fol.add_expr('x')
    p = fol.pick(u, care_vars=['x'])
    for i in range(10):
        q = fol.pick(u, care_vars=['x'])
        assert p == q, (p, q)
    u = fol.add_expr('False')
    p = fol.pick(u, care_vars=['x'])
    assert p is None, p


def test_pick_iter():
    fol = _fol.Context()
    fol.declare(x='bool', y=(0, 2))
    u = fol.add_expr('True')
    gen = fol.pick_iter(u, care_vars=['x'])
    r = list(gen)
    assert len(r) == 2, r
    u = fol.add_expr('False')
    gen = fol.pick_iter(u, care_vars=['x'])
    r = list(gen)
    assert len(r) == 0, r
    u = fol.add_expr('x')
    gen = fol.pick_iter(u, care_vars=['x'])
    r = list(gen)
    assert len(r) == 1, r
    u = fol.add_expr('x')
    gen = fol.pick_iter(u, care_vars=['x', 'y'])
    r = list(gen)
    assert len(r) == 4, r


def test_define():
    c = _fol.Context()
    c.declare(x=(9, 35))
    c.declare(y=(1, 5))
    c.declare(z=(-3, 10))
    e = '''
        a == x + y > 3
        b == z - x <= 0
        c == a /\ b
        '''
    c.define(e)
    # pprint.pprint(c.op)
    # a
    s = c.op['a']
    s_ = '( ( x + y ) > 3 )'
    assert s == s_, s
    u = c.op_bdd['a']
    u_ = c.add_expr(s_)
    assert u == u_, u
    # b
    s = c.op['b']
    s_ = '( ( z - x ) <= 0 )'
    assert s == s_, s
    u = c.op_bdd['b']
    u_ = c.add_expr(s_)
    assert u == u_, u
    # c
    s = c.op['c']
    s_ = '( a /\ b )'
    assert s == s_, s
    u = c.op_bdd['c']
    # caution:  operator names *have* been substituted in
    # the BDD, unlike the expression in `c.op['c']` above.
    s_ = '( ( ( x + y ) > 3 )  /\  ( ( z - x ) <= 0 ) )'
    u_ = c.add_expr(s_)
    assert u == u_, u


def test_add_expr():
    fol = _fol.Context()
    bdd = fol.bdd
    u = fol.add_expr('False')
    assert u == bdd.false, bdd.to_expr(u)
    fol.declare(x=(0, 100), y=(5, 23))
    u = fol.add_expr('x < y + 5')
    v = fol.add_expr('x - 5 < y')
    assert u == v, (u, v)


def test_to_expr():
    fol = _fol.Context()
    fol.bdd.configure(reordering=True)
    fol.declare(x=(-14, 100), y=(5, 23))
    u = fol.add_expr('(1 <= x) /\ (x <= 3)')
    s = fol.to_expr(u, show_limits=True)
    s_ = ' /\\ x \\in -128 .. 127\n /\\ (x \in 1 .. 3)'
    assert s == s_, (s, s_)
    care = fol.add_expr('(-14 <= x)  /\  (x <= 100)')
    s = fol.to_expr(u, care=care, show_dom=True)
    s_ = (
        ' /\\ x \\in -14 .. 100\n'
        ' /\\ (x \in 1 .. 3)\n'
        ' /\\ care expression')
    assert s == s_, (s, s_)


def test_apply():
    fol = _fol.Context()
    bdd = fol.bdd
    fol.declare(x='bool')
    u = fol.add_expr('x')
    v = fol.add_expr('! x')
    w = fol.apply('and', u, v)
    assert w == bdd.false
    w = fol.apply('or', u, v)
    assert w == bdd.true


def test_reorder():
    fol = _fol.Context()
    bdd = fol.bdd
    fol.declare(x=(0, 7), y=(0, 3))
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
