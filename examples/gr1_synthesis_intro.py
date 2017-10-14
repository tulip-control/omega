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
from omega.symbolic import temporal as trl


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
    aut = trl.Automaton()
    aut.declare_variables(x=(1, 3), y=(-3, 3))
    aut.varlist.update(env=['x'], sys=['y'])
    aut.init['env'] = 'x = 1'
    aut.init['sys'] = 'y = 2'
    aut.action['env'] = '''
        /\ x \in 1..2
        /\ x' \in 1..2
        '''
    aut.action['sys'] = '''
        /\ y \in -3..3
        /\ y' = x - 3
        '''
    aut.win['<>[]'] = aut.bdds_from('x = 2')
    aut.win['[]<>'] = aut.bdds_from('y != -1')
    aut.qinit = '\E \A'
    aut.moore = True
    aut.plus_one = True
    return aut


def synthesize_some_controller(aut):
    """Return a controller that implements the spec.

    If no controller exists, then raise an `Exception`.
    The returned controller is represented as a `networkx` graph.
    """
    z, yij, xijk = gr1.solve_streett_game(aut)
    gr1.make_streett_transducer(z, yij, xijk, aut)
    g = enum.action_to_steps(
        aut, env='env', sys='impl', qinit=aut.qinit)
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
