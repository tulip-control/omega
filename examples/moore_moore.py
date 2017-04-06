#!/usr/bin/env python
"""Synthesize two Moore implementations, and simulate their assembly."""
from matplotlib import pyplot as plt
from omega.games import gr1
from omega.logic import syntax as stx
from omega import steps
from omega.symbolic import temporal as trl


def main():
    """Synthesize two Moore components, assemble, and simulate them."""
    # synthesize
    foo_spec = specify_component_foo()
    bar_spec = specify_component_bar()
    synthesize_some_controller('bar', 'foo', foo_spec)
    synthesize_some_controller('foo', 'bar', bar_spec)
    # assemble
    foo = steps.AutomatonStepper(foo_spec)
    bar = steps.AutomatonStepper(bar_spec)
    sch = steps.Scheduler(2)
    asm = steps.Assembly()
    asm.machines = dict(scheduler=sch, foo=foo, bar=bar)
    # history
    n_steps = 15
    asm.init()
    print(asm.state)
    for _ in range(n_steps):
        asm.step()
        print(asm.state)
    # plotting
    plot_machines(asm)
    plt.xlabel('behavior states')
    plt.show()


def specify_component_foo():
    """Return temporal logic spec of component foo."""
    aut = trl.Automaton()
    aut.players = ['foo', 'bar', 'scheduler']
    aut.declare_variables(x=(0, 1), y=(0, 1), turn=(0, 1))
    aut.varlist['scheduler'] = ['turn']
    aut.varlist['foo'] = ['x']
    aut.varlist['bar'] = ['y']
    spec = r'''
    FooInit == x = 1
    BarInit == y = 1 /\ turn = 1

    FooNext ==
        /\ ((x = 1) \/ (y = 1))
        /\ (x \in 0..1  /\  x' \in 0..1)
        /\ ((turn != 0) => (x' = x))
    BarNext ==
        /\ ((x = 1) \/ (y = 1))
        /\ ((x = 0) => (y' = 1))
        /\ (y \in 0..1) /\ (y' \in 0..1)
        /\ ((turn = 0) => (y' = y))
        /\ (turn' != turn)
    '''
    aut.define(spec)
    aut.init.update(
        foo='FooInit',
        bar='BarInit')
    aut.action.update(
        foo='FooNext',
        bar='BarNext')
    aut.win = dict(
        foo={'<>[]': aut.bdds_from('y = 0', 'turn = 0', 'turn = 1'),
             '[]<>': aut.bdds_from('x = 0', 'x = 1')})
    aut.qinit = r'\E \A'
    aut.moore = True
    aut.plus_one = True
    return aut


def specify_component_bar():
    """Return temporal logic spec of component bar."""
    aut = trl.Automaton()
    aut.players = ['foo', 'bar', 'scheduler']
    aut.declare_variables(x=(0, 1), y=(0, 1), turn=(0, 1))
    aut.varlist['scheduler'] = ['turn']
    aut.varlist['foo'] = ['x']
    aut.varlist['bar'] = ['y']
    spec = r'''
    FooInit == x = 1 /\ turn = 1
    BarInit == y = 1

    FooNext ==
        /\ ((x = 1) \/ (y = 1))
        /\ ((y = 0) => (x' = 1))
        /\ (x \in 0..1) /\ (x' \in 0..1)
        /\ ((turn = 1) => (x' = x))
        /\ (turn' != turn)
    BarNext ==
        /\ ((x = 1) \/ (y = 1))
        /\ (y \in 0..1  /\  y' \in 0..1)
        /\ ((turn != 1) => (y' = y))
    '''
    aut.define(spec)
    aut.init.update(
        foo='FooInit',
        bar='BarInit')
    aut.action.update(
        foo='FooNext',
        bar='BarNext')
    aut.win = dict(
        bar={'<>[]': aut.bdds_from('x = 0', 'turn = 0', 'turn = 1'),
             '[]<>': aut.bdds_from('y = 0', 'y = 1')})
    aut.qinit = r'\E \A'
    aut.moore = True
    aut.plus_one = True
    return aut


def synthesize_some_controller(env, sys, aut):
    """Return a controller that implements the spec.

    If no controller exists, then raise an `Exception`.
    The returned controller is represented as a `networkx` graph.
    """
    aut.prime_varlists()
    # vars
    aut.varlist['env'] = aut.varlist[env] + aut.varlist['scheduler']
    aut.varlist['sys'] = aut.varlist[sys]
    # init
    aut.init['env'] = aut.init[env]
    aut.init['sys'] = aut.init[sys]
    # actions
    aut.action['env'] = aut.action[env]
    aut.action['sys'] = aut.action[sys]
    # win
    aut.win['[]<>'] = aut.win[sys]['[]<>']
    aut.win['<>[]'] = aut.win[sys]['<>[]']
    z, yij, xijk = gr1.solve_streett_game(aut)
    gr1.make_streett_transducer(z, yij, xijk, aut)
    aut.varlist[sys].append('_goal')
    aut.prime_varlists()


def plot_machines(asm):
    """Plot machine behaviors over a finite number of steps."""
    nrows = len(asm.machines)
    history = asm.past + [asm.state]
    n_steps = len(history)  # missing last state
    t = range(n_steps)
    plt.subplots(nrows=nrows, ncols=1)
    styles = ['b-o', 'r--', 'k-', 'g-*']  # def style picker
    for i, (name, stm) in enumerate(asm.machines.items()):
        plt.subplot(nrows, 1, i + 1)
        plt.title(name)
        styles_cp = list(styles)
        # TODO: could instead plot only sys vars and memory
        for var in stm.vars:
            if stx.isprimed(var):
                continue
            x = [steps.omit_prefix(state, name)[var]
                 for state in history]
            style = styles_cp.pop()
            plt.plot(t, x, style, label=var)
        plt.legend()
        plt.grid()


if __name__ == '__main__':
    main()
