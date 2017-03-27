"""How to write generalized reactivity(1) specifications.

In this elementary example we write what we want in mathematics
(using temporal logic) and an algorithm finds a step-by-step
program that does it. The generated program is described by a graph.
"""
import logging

import networkx as nx
from omega.games import gr1
from omega.games import enumeration as enum
from omega.symbolic import enumeration as sym_enum
from omega.symbolic import symbolic


log = logging.getLogger('omega.games.enumeration')
log.addHandler(logging.StreamHandler())
log.setLevel(logging.DEBUG)


def solve_design_problem():
    """Synthesize a controller from a mathematical specification."""
    spec = gr1_specification()
    controller = synthesize_some_controller(spec)
    print_info(controller)
    dump_graph_as_figure(controller)


def gr1_specification():
    """Return a temporal logic spec in the GR(1) fragment."""
    aut = symbolic.Automaton()
    aut.vars = dict(
        x=dict(type='int', dom=(1, 3), owner='env'),
        y=dict(type='int', dom=(-3, 3), owner='sys'))
    aut.init['env'] = ['x = 1  /\  y = 2']
    aut.init['sys'] = ['TRUE']
    aut.action['env'] = ['''
        1 <= x  /\  x <= 2
        ''']
    aut.action['sys'] = ['''
        /\ -3 <= y
        /\ y <= 3
        /\ y' = x - 3
        ''']
    aut.win['<>[]'] = ['x = 2']
    aut.win['[]<>'] = ['y != -1']
    aut.qinit = '\A \A'  # should work from all states that
                         # satisfy `aut.init['env']`
    aut.moore = True
    aut.plus_one = True
    return aut


def synthesize_some_controller(aut):
    """Return a controller that implements the spec.

    If no controller exists, then raise an `Exception`.
    The returned controller is represented as a `networkx` graph.
    """
    qinit = aut.qinit
    aut_compiled = aut.build()  # compile expression strings to BDDs
    z, yij, xijk = gr1.solve_streett_game(aut_compiled)
    t = gr1.make_streett_transducer(z, yij, xijk, aut_compiled)
    g = enum.action_to_steps(t, qinit=qinit)
    return g


def print_info(g):
    print('Enumerated strategy has {n} nodes.'.format(
        n=len(g)))
    print('The nodes are:')
    print(g.nodes(data=True))
    print('The edges (transitions) are:')
    print(g.edges(data=True))


def dump_graph_as_figure(g):
    """Create a PDF file showing the graph `g`."""
    h, _ = sym_enum._format_nx(g)
    pd = nx.drawing.nx_pydot.to_pydot(h)
    pd.write_pdf('game_states.pdf')


if __name__ == '__main__':
    solve_design_problem()
