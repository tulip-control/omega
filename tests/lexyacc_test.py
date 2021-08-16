"""Tests for `omega.logic.lexyacc."""
from omega.logic import lexyacc


parser = lexyacc.Parser()


def test_existential_quantifier():
    # with one quantified constant
    _check_quantifier_1_decl(r'\E x:  True', 'True')
    _check_quantifier_1_decl(r'\E x:  TRUE', 'TRUE')
    _check_quantifier_1_decl(r'\E x:  False', 'False')
    _check_quantifier_1_decl(r'\E x:  FALSE', 'FALSE')
    # with two quantified constants
    _check_quantifier_2_decl(r'\E x, y:  True', 'True')
    _check_quantifier_2_decl(r'\E x, y:  TRUE', 'TRUE')
    _check_quantifier_2_decl(r'\E x, y:  False', 'False')
    _check_quantifier_2_decl(r'\E x, y:  FALSE', 'FALSE')


def _check_quantifier_1_decl(expr, literal):
    tree = parser.parse(expr)
    assert hasattr(tree, 'operator'), tree
    assert tree.type == 'operator', tree
    assert tree.operator == r'\E', tree.operator
    assert len(tree.operands) == 2, tree.operands
    qvars, predicate = tree.operands
    assert hasattr(qvars, 'operator'), qvars
    assert qvars.operator == 'params', qvars.operator
    x, = qvars.operands
    _assert_is_var_node(x, 'x')
    assert hasattr(predicate, 'type'), predicate
    assert predicate.type == 'bool', predicate.type
    assert predicate.value == literal, predicate.value


def _check_quantifier_2_decl(expr, literal):
    tree = parser.parse(expr)
    assert hasattr(tree, 'type'), t
    assert tree.type == 'operator', tree.type
    assert tree.operator == r'\E', tree.operator
    assert len(tree.operands) == 2, tree.operands
    qvars, predicate = tree.operands
    assert hasattr(qvars, 'operator'), qvars
    assert qvars.operator == 'params', qvars.operator
    x, y = qvars.operands
    _assert_is_var_node(x, 'x')
    _assert_is_var_node(y, 'y')
    assert hasattr(predicate, 'type'), predicate
    assert predicate.type == 'bool', predicate.type
    assert predicate.value == literal, predicate.value


def test_universal_quantifier():
    s = r'\A y:  True'
    t = parser.parse(s)
    assert t.operator == r'\A', t.operator
    #
    s = r'\A x, y, z:  (x \/ ~ y) /\ z'
    t = parser.parse(s)
    assert t.operator == r'\A', t.operator
    assert len(t.operands) == 2, t.operands
    qvars, e = t.operands
    assert hasattr(qvars, 'operator'), qvars
    assert qvars.operator == 'params', qvars.operator
    x, y, z = qvars.operands
    _assert_is_var_node(x, 'x')
    _assert_is_var_node(y, 'y')
    _assert_is_var_node(z, 'z')
    r = e.flatten()
    r_ = r'( ( x \/ ( ~ y ) ) /\ z )'
    assert r == r_, (r, r_)


def test_substitution():
    s = r'\S a / b: True'
    t = parser.parse(s)
    assert hasattr(t, 'type'), t
    assert t.type == 'operator', t.type
    assert t.operator == r'\S', t.operator
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
    s = r'\S a / b,  c / d: False'
    t = parser.parse(s)
    assert hasattr(t, 'type'), t
    assert t.type == 'operator', t
    assert t.operator == r'\S', t.operator
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
        r'( ( z \in ( 0 .. 2 ) )'
        r' /\ ( y \in ( -45 .. 1 ) ) )')
    assert r == r_, r


def test_multiline_tla_comment():
    # on single line
    s = '(* this is a comment *) a = 1'
    r = parser.parse(s).flatten()
    r_ = '( a = 1 )'
    assert r == r_, r
    # spread over multiple lines
    s = '(* hohoho \n bar bar foo *) a = 1'
    r = parser.parse(s).flatten()
    r_ = '( a = 1 )'
    assert r == r_, r
    # repeated
    s = '(* foo *) a = 1 (* bar *)'
    r = parser.parse(s).flatten()
    r_ = '( a = 1 )'
    assert r == r_, r


def _assert_is_var_node(x, var):
    assert hasattr(x, 'type'), x
    assert x.type == 'var', x.type
    assert x.value == var, x.value


if __name__ == '__main__':
    test_range()
