#!/usr/bin/env python
from omega.symbolic import codegen as dump
from omega.symbolic import fol as _fol
from omega.symbolic import functions as fcn
from omega.symbolic import temporal as trl


def test_functional_synthesis():
    aut = trl.Automaton()
    aut.declare_variables(x=(1, 10))
    aut.declare_variables(y=(1, 10))
    x_bits = aut.vars['x']['bitnames']
    y_bits = aut.vars['y']['bitnames']
    u = aut.to_bdd('x = y')
    outputs = fcn.make_functions(u, y_bits, aut.bdd)
    for x_bit, y_bit in zip(x_bits, y_bits):
        x_bdd = aut.bdd.add_expr(x_bit)
        y_bdd = outputs[y_bit]['function']
        assert x_bdd == y_bdd, (x_bit, y_bit)


def test_code_generation():
    aut = trl.Automaton()
    aut.declare_variables(x=(1, 6), y=(1, 6))
    u = aut.to_bdd(" y' = (x - y) ")
    out_vars = ["y'"]
    code = dump.dumps_bdds_as_code(u, out_vars, aut)
    file_name = 'generated_foo.py'
    with open(file_name, 'w') as f:
        f.write(code)
    from generated_foo import step  # load generated code
    state = dict(x=3, y=3)
    out_vars = step(state)
    out_vars_ = {"y'": 0}
    assert out_vars == out_vars_, out_vars
    state = dict(x=2, y=1)
    out_vars = step(state)
    out_vars_ = {"y'": 1}
    assert out_vars == out_vars_, out_vars
    state = dict(x=5, y=3)
    out_vars = step(state)
    out_vars_ = {"y'": 2}
    assert out_vars == out_vars_, out_vars
    state = dict(x=1, y=0)
    out_vars = step(state)
    out_vars_ = {"y'": 1}
    assert out_vars == out_vars_, out_vars


def test_dump_bdd_as_code():
    bdd = _fol._bdd.BDD()
    bdd.declare('x', 'y')
    u = bdd.add_expr('x /\ ~ y')
    roots = dict(output=u)
    code = dump.dumps_bdd_as_code(roots, bdd)
    boolean = [False, True]
    for x in boolean:
        for y in boolean:
            state = dict(x=x, y=y, out_bits=dict())
            exec(code, state)
            out = state['out_bits']['output']
            assert out == (x and not y), out
    # a longer formula
    bdd.declare('x', 'y', 'z', 'w')
    u = bdd.add_expr('(x /\ y) \/ (~ z) \/ (w /\ (x \/ y))')
    roots = dict(output=u)
    code = dump.dumps_bdd_as_code(roots, bdd)
    state = dict(x=True, y=False, z=True, w=True,
                 out_bits=dict())
    exec(code, state)
    out = state['out_bits']['output']
    assert out == True, out


if __name__ == '__main__':
    test_dump_bdd_as_code()
