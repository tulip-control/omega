"""Solving a game to win a Streett(1) specification."""
import logging

import networkx as nx
from omega.symbolic import logicizer
from omega.symbolic import enumeration as sym_enum
from omega.games import gr1
from omega.games import enumeration as enum
from omega.automata import TransitionSystem


log = logging.getLogger('omega.games.enumeration')
log.addHandler(logging.StreamHandler())
log.setLevel(logging.DEBUG)


def semi_symbolic():
    """Example using a semi-enumerated state machine.

    Instructive variants:

    - `formula = "x'"`
    - `self_loops = True`
    - `aut.moore = False`
    """
    g = TransitionSystem()
    g.owner = 'sys'
    g.vars = dict(x='bool')
    g.env_vars.add('x')
    nx.add_path(g, range(11))
    g.add_edge(10, 10)
    g.add_edge(10, 0, formula="x")
    # symbolic
    aut = logicizer.graph_to_logic(
        g, 'nd', ignore_initial=True, self_loops=False)
    aut.init['env'] = 'nd = 1'
    aut.win['<>[]'] = aut.bdds_from(' ~ x')
    aut.win['[]<>'] = aut.bdds_from('nd = 0')
    aut.qinit = r'\A \A'
    aut.moore = True
    aut.plus_one = True
    print(aut)
    # compile to BDD
    z, yij, xijk = gr1.solve_streett_game(aut)
    gr1.make_streett_transducer(z, yij, xijk, aut)
    # print t.bdd.to_expr(t.action['sys'][0])
    r = aut.action['sys']
    # aut.bdd.dump('bdd.pdf', roots=[r])
    g = enumerate_controller(aut)
    h, _ = sym_enum._format_nx(g)
    pd = nx.drawing.nx_pydot.to_pydot(h)
    pd.write_pdf('game_states.pdf')
    print('Enumerated strategy has {n} nodes.'.format(
        n=len(g)))
    print(('Winning set:', aut.bdd.to_expr(z)))
    print('{n} BDD nodes in total'.format(
        n=len(aut.bdd)))


def enumerate_controller(aut):
    g = enum.action_to_steps(
        aut, env='env', sys='impl', qinit=aut.qinit)
    return g


if __name__ == '__main__':
    semi_symbolic()
