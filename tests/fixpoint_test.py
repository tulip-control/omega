from omega.automata import TransitionSystem
from omega.symbolic import fixpoint as fx
from omega.symbolic import logicizer, symbolic


def test_descendants():
    g = TransitionSystem()
    g.add_path([0, 1, 2])
    a = logicizer.graph_to_logic(g, 'pc', True)
    symbolic.fill_blanks(a)
    aut = a.build()
    source = aut.add_expr('pc = 0')
    constrain = aut.bdd.True
    v = fx.descendants(source, constrain, aut)
    assert v == aut.bdd.add_expr('pc_0 ^ pc_1'), aut.bdd.to_expr(v)


def test_ee_image_only_sys():
    g = TransitionSystem()
    g.add_path([0, 1, 2])
    a = logicizer.graph_to_logic(g, 'pc', True)
    symbolic.fill_blanks(a)
    aut = a.build()
    u = aut.add_expr('pc = 0')
    v = fx.ee_image(u, aut)
    v_ = aut.add_expr('pc = 1')
    assert v == v_, a.bdd.to_expr(v)
    v = fx.ee_image(v, aut)
    v_ = aut.add_expr('pc = 2')
    assert v == v_, aut.bdd.to_expr(v)


def test_ue_image_no_constrain():
    g = TransitionSystem()
    g.vars = dict(x='bool')
    g.env_vars = {'x'}
    g.add_edge(0, 1, formula='x')
    g.add_edge(0, 2, formula='!x')
    a = logicizer.graph_to_logic(g, 'pc', True)
    symbolic.fill_blanks(a)
    aut = a.build()
    # source constrained to x
    source = aut.add_expr('x & (pc = 0)')
    u = fx.ee_image(source, aut)
    assert u == aut.add_expr('pc = 1')
    # source contains both x and ! x
    source = aut.add_expr('pc = 0')
    u = fx.ee_image(source, aut)
    assert u == aut.add_expr('(pc = 1) | (pc = 2)')


def test_ee_image():
    g = TransitionSystem()
    g.vars = dict(x='bool')
    g.env_vars = {'x'}
    g.add_edge(0, 1, formula='x')
    g.add_edge(0, 1, formula='!x')
    g.add_edge(0, 2, formula='x')
    a = logicizer.graph_to_logic(g, 'pc', True)
    symbolic.fill_blanks(a)
    aut = a.build()
    source = aut.add_expr('pc = 0')
    u = fx.ee_image(source, aut)
    u_ = aut.add_expr('(pc = 1) | (pc = 2)')
    assert u == u_, aut.bdd.to_expr(u)


def test_ue_preimage():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='env'),
                  y=dict(type='bool', owner='sys'))
    a.action['sys'] = ["x' -> !y'"]
    symbolic.fill_blanks(a)
    aut = a.build()
    target = aut.add_expr('y')
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    u = fx.ue_preimage(env_action, sys_action, target, aut)
    assert u == aut.bdd.False, aut.bdd.to_expr(u)
    u = fx.ue_preimage(env_action, sys_action, target, aut,
                       evars=aut.uepvars)
    assert u == aut.bdd.True, aut.bdd.to_expr(u)


if __name__ == '__main__':
    test_ue_preimage()
