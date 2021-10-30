"""Test the module `omega.steps`."""
import omega.steps as steps
import omega.symbolic.temporal as trl
import pytest


def test_step():
    aut = trl.Automaton()
    aut.declare_variables(x='bool', y=(1, 3))
    aut.varlist = dict(env=['x'], sys=['y'], impl=[])
    aut.prime_varlists()
    aut.init['impl'] = 'TRUE'
    action = aut.add_expr(r"x /\ (~ x') /\ (y = 2) /\ (y' = 3)")
    aut.action['impl'] = action
    stepper = steps.AutomatonStepper(aut)
    # `action` enabled at `state`
    state = dict(x=True, y=2)
    next_values = stepper.step(state)
    d = dict(x=False, y=3)
    assert next_values == d, (next_values, d)
    # `action` not enabled at `state`
    state = dict(x=True, y=1)
    with pytest.raises(ValueError):
        stepper.step(state)


def test_omit_prefix():
    d = {'a': 1, 'foo_mem': 3}
    prefix = 'foo'
    r = steps.omit_prefix(d, prefix)
    r_ = {'a': 1, '_mem': 3}
    assert r == r_, (r, r_)
    # name conflict
    d = {'a': 1, '_mem': 2, 'foo_mem': 3}
    with pytest.raises(AssertionError):
        steps.omit_prefix(d, prefix)


if __name__ == '__main__':
    test_component()
