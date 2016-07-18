from omega.symbolic import logicizer
from omega.games import gr1
from omega.automata import TransitionSystem


def semi_symbolic():
    g = TransitionSystem()
    g.owner = 'sys'
    g.vars = dict(x='bool')
    g.env_vars.add('x')
    g.add_path(xrange(11))
    g.add_edge(10, 0, formula="x'")
    g.initial_nodes.add(0)
    # symbolic
    a = logicizer.graph_to_logic(
        g, 'nd', ignore_initial=False, self_loops=True)
    a.win['<>[]'].append('!x')
    a.win['[]<>'].append('nd = 0')
    print(a)
    # compile to BDD
    aut = a.build()
    aut.moore = True
    aut.plus_one = True
    z, yij, xijk = gr1.solve_streett_game(aut)
    t = gr1.make_streett_transducer(z, yij, xijk, aut)
    # print t.bdd.to_expr(t.action['sys'][0])
    r = t.action['sys'][0]
    t.bdd.dump('bdd.pdf', roots=[r])
    print('Winning set:', aut.bdd.to_expr(z))
    print('Total number of BDD nodes: {n}'.format(
        n=len(t.bdd)))


if __name__ == '__main__':
    semi_symbolic()
