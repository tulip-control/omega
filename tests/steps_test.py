"""Test the module `omega.steps`."""
from nose import tools as nt
from omega import steps
from omega.symbolic import temporal as trl


def test_step():
    aut = trl.Automaton()
    aut.declare_variables(x='bool', y=(1, 3))
    aut.varlist = dict(env=['x'], sys=['y'], impl=[])
    aut.prime_varlists()
    aut.init['impl'] = 'True'
    action = aut.add_expr("x /\ (~ x') /\ (y = 2) /\ (y' = 3)")
    aut.action['impl'] = action
    stepper = steps.AutomatonStepper(aut)
    # `action` enabled at `state`
    state = dict(x=True, y=2)
    next_values = stepper.step(state)
    d = dict(x=False, y=3)
    assert next_values == d, (next_values, d)
    # `action` not enabled at `state`
    state = dict(x=True, y=1)
    with nt.assert_raises(ValueError):
        stepper.step(state)


def test_omit_prefix():
    d = {'a': 1, 'foo_mem': 3}
    prefix = 'foo'
    r = steps.omit_prefix(d, prefix)
    r_ = {'a': 1, '_mem': 3}
    assert r == r_, (r, r_)
    # name conflict
    d = {'a': 1, '_mem': 2, 'foo_mem': 3}
    with nt.assert_raises(AssertionError):
        steps.omit_prefix(d, prefix)


if __name__ == '__main__':
    test_component()
