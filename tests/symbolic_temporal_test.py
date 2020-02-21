"""Test `omega.symbolic.temporal`."""
from omega.symbolic import temporal as trl


def test_declare_variables():
    aut = trl.Automaton()
    aut.declare_variables(x=(0, 5), y='bool')
    assert 'x' in aut.vars, aut.vars
    assert "x'" in aut.vars, aut.vars
    assert 'y' in aut.vars, aut.vars
    assert "y'" in aut.vars, aut.vars


def test_declare_constants():
    aut = trl.Automaton()
    aut.declare_constants(x=(0, 5), y='bool')
    assert 'x' in aut.vars, aut.vars
    assert "x'" not in aut.vars, aut.vars
    assert 'y' in aut.vars, aut.vars
    assert "y'" not in aut.vars, aut.vars


def test_add_vars():
    aut = trl.Automaton()
    aut.add_vars(
        {'x': {'type': 'int', 'dom': (0, 5)}},
        flexible=False)
    aut.add_vars(
        {'y': {'type': 'bool'}},
        flexible=True)
    assert 'x' in aut.vars, aut.vars
    assert "x'" not in aut.vars, aut.vars
    assert 'y' in aut.vars, aut.vars
    assert "y'" in aut.vars, aut.vars


def test_vars_of_players():
    aut = trl.Automaton()
    aut.varlist.update(env=['x'], sys=['y'])
    vrs = aut.vars_of_players({'env'})
    vrs_ = {'x'}
    assert vrs == vrs_, vrs
    vrs = aut.vars_of_players({'env', 'sys'})
    vrs_ = {'x', 'y'}
    assert vrs == vrs_, vrs
    vrs = aut.vars_of_all_players
    assert vrs == set(), vrs
    aut.players.update(env=0, sys=1)
    vrs = aut.vars_of_all_players
    assert vrs == vrs_, vrs


def test_prime_varlists():
    aut = trl.Automaton()
    aut.varlist.update(env=['x'], sys=['y'])
    aut.prime_varlists()
    assert "env'" in aut.varlist, aut.varlist
    assert aut.varlist["env'"] == ["x'"], aut.varlist
    assert "sys'" in aut.varlist, aut.varlist
    assert aut.varlist["sys'"] == ["y'"], aut.varlist


def test_replace_with_primed():
    aut = trl.Automaton()
    aut.declare_variables(x=(0, 10), y=(0, 10))
    aut.declare_constants(z='bool')
    u = aut.add_expr("(x = 1 /\ y = 2) \/ ~ z")
    vrs = ['x', 'y']
    v = aut.replace_with_primed(vrs, u)
    v_ = aut.add_expr("(x' = 1 /\ y' = 2) \/ ~ z")
    assert v == v_, list(aut.pick_iter(v))


def test_replace_with_unprimed():
    aut = trl.Automaton()
    aut.declare_variables(x=(0, 10), y=(0, 10))
    aut.declare_constants(z='bool')
    u = aut.add_expr("(x' = 1 /\ y' = 2) \/ ~ z")
    vrs = ['x', 'y']
    v = aut.replace_with_unprimed(vrs, u)
    v_ = aut.add_expr("(x = 1 /\ y = 2) \/ ~ z")
    assert v == v_, list(aut.pick_iter(v))


def test_implies_type_hints():
    aut = trl.Automaton()
    aut.declare_variables(
        x=(0, 10), y=(0, 10), z='bool')
    u = aut.add_expr('x \in 0..10 /\ y \in 0..10')
    assert aut.implies_type_hints(u)
    assert aut.implies_type_hints(u, vrs=['x', 'y'])
    u = aut.add_expr('x \in 0..12 /\ y \in 0..10')
    assert not aut.implies_type_hints(u)
    u = aut.add_expr('y \in 0..10')
    assert not aut.implies_type_hints(u)
    assert aut.implies_type_hints(u, vrs=['y'])


def test_type_hint_for():
    aut = trl.Automaton()
    aut.declare_variables(
        x=(0, 10), y=(0, 10), z='bool')
    t = aut.type_hint_for(['x', 'y'])
    t_ = (
        '((0 <= x) /\ (x  <= 10)) '
        '/\ ((0 <= y) /\ (y  <= 10))')
    assert t == t_, t


def test_type_action_for():
    aut = trl.Automaton()
    aut.declare_variables(
        x=(0, 10), y=(0, 10), z='bool')
    t = aut.type_action_for(['x', 'y'])
    t_ = (
        "(((0 <= x) /\ (x  <= 10)) "
        "/\ ((0 <= x') /\ (x'  <= 10))) "
        "/\ (((0 <= y) /\ (y  <= 10)) "
        "/\ ((0 <= y') /\ (y'  <= 10)))")
    assert t == t_, t


if __name__ == '__main__':
    test_type_action_for()
