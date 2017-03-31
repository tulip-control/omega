"""Test `omega.symbolic.fixpoint`."""
import logging

logging.getLogger('omega').setLevel(logging.WARNING)

from omega.automata import TransitionSystem
from omega.symbolic import fixpoint as fx
from omega.symbolic import fol as _fol
from omega.symbolic import logicizer
from omega.symbolic import symbolic


def test_attractor():
    g = TransitionSystem()
    g.vars['x'] = 'bool'
    g.env_vars.add('x')
    g.add_path([0, 1, 2, 3])
    g.add_edge(4, 1, formula='x')
    a = logicizer.graph_to_logic(g, 'loc', True)
    symbolic.fill_blanks(a)
    aut = a.build()
    target = aut.add_expr('loc = 2')
    u = fx.attractor(aut.action['env'][0], aut.action['sys'][0],
                     target, aut)
    fol = _fol.Context()
    fol.add_vars(aut.vars)
    fol.bdd = aut.bdd
    bdd = aut.bdd
    ok = {0: True, 1: True, 2: True, 3: False, 4: False}
    for q, value in ok.items():
        subs = {'loc': q}
        v = fol.let(subs, u)
        assert (v == bdd.true) == value, v
    inside = aut.add_expr('loc > 0')
    u = fx.attractor(aut.action['env'][0], aut.action['sys'][0],
                     target, aut, inside=inside)
    ok = {0: False, 1: True, 2: True, 3: False, 4: False}
    for q, value in ok.items():
        subs = {'loc': q}
        v = fol.let(subs, u)
        assert (v == bdd.true) == value, v


def test_descendants():
    g = TransitionSystem()
    g.add_path([0, 1, 2])
    a = logicizer.graph_to_logic(g, 'pc', True)
    symbolic.fill_blanks(a)
    aut = a.build()
    source = aut.add_expr('pc = 0')
    constrain = aut.bdd.true
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


def test_cpre_moore_plus_one():
    cpre = fx.ue_preimage
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='env'),
                  y=dict(type='bool', owner='sys'))
    a.moore = True
    a.plus_one = True
    bdd = a.bdd
    # no env
    # y'
    a.action['env'] = ["True"]
    a.action['sys'] = ["y'"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = aut.add_expr('True')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.true
    target = aut.add_expr('False')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false
    target = aut.add_expr('y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.true
    target = aut.add_expr('! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false
    # y
    a.action['env'] = ["True"]
    a.action['sys'] = ["y"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = aut.add_expr('True')
    y =  bdd.add_expr('y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == y, bdd.to_expr(u)
    target = aut.add_expr('False')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false, bdd.to_expr(u)
    target = aut.add_expr('y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == y, bdd.to_expr(u)
    target = aut.add_expr('! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == y, bdd.to_expr(u)
    # with env
    # x => y'
    a.action['env'] = ["True"]
    a.action['sys'] = ["x => y'"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = aut.add_expr('y')
    y =  bdd.add_expr('y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.true, bdd.to_expr(u)
    target = aut.add_expr('! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.add_expr('! x'), bdd.to_expr(u)
    target = aut.add_expr('False')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false, bdd.to_expr(u)
    # x' => y'
    a.action['env'] = ["True"]
    a.action['sys'] = ["x' => y'"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = aut.add_expr('True')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.true, bdd.to_expr(u)
    target = aut.add_expr('y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.true, bdd.to_expr(u)
    target = aut.add_expr('! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false, bdd.to_expr(u)
    # x' => y' with assumption
    a.action['env'] = ["! x'"]
    a.action['sys'] = ["x' => y'"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    # `plus_one` cannot depend on `x`
    target = aut.add_expr('! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false, bdd.to_expr(u)
    # x => y' with assumption
    a.action['env'] = ["! x'"]
    a.action['sys'] = ["x => y'"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = aut.add_expr('! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.add_expr('! x'), bdd.to_expr(u)
    target = aut.add_expr('x & ! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false, bdd.to_expr(u)
    target = aut.add_expr('! x & ! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.add_expr('! x'), bdd.to_expr(u)


def test_cpre_moore_circular():
    cpre = fx.ue_preimage
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='env'),
                  y=dict(type='bool', owner='sys'))
    a.moore = True
    a.plus_one = False
    bdd = a.bdd
    # no env
    # y'
    a.action['env'] = ["True"]
    a.action['sys'] = ["y'"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = aut.add_expr('True')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.true
    target = aut.add_expr('False')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false
    target = aut.add_expr('y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.true
    target = aut.add_expr('! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false
    # y
    a.action['env'] = ["True"]
    a.action['sys'] = ["y"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = aut.add_expr('True')
    y =  bdd.add_expr('y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == y, bdd.to_expr(u)
    target = aut.add_expr('False')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false, bdd.to_expr(u)
    target = aut.add_expr('y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == y, bdd.to_expr(u)
    target = aut.add_expr('! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == y, bdd.to_expr(u)
    # with env
    # x => y'
    a.action['env'] = ["True"]
    a.action['sys'] = ["x => y'"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = aut.add_expr('y')
    y =  bdd.add_expr('y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.true, bdd.to_expr(u)
    target = aut.add_expr('! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.add_expr('! x'), bdd.to_expr(u)
    target = aut.add_expr('False')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false, bdd.to_expr(u)
    # x' => y'
    a.action['env'] = ["True"]
    a.action['sys'] = ["x' => y'"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = aut.add_expr('True')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.true, bdd.to_expr(u)
    target = aut.add_expr('y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.true, bdd.to_expr(u)
    target = aut.add_expr('! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false, bdd.to_expr(u)
    # x' => y' with assumption
    a.action['env'] = ["x"]
    a.action['sys'] = ["x' => y'"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    # circular
    target = aut.add_expr('! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.add_expr('! x'), bdd.to_expr(u)
    # x => y' with assumption
    a.action['env'] = ["! x'"]
    a.action['sys'] = ["x => y'"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = aut.add_expr('! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.add_expr('! x'), bdd.to_expr(u)
    target = aut.add_expr('x & ! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false, bdd.to_expr(u)
    target = aut.add_expr('! x & ! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.add_expr('! x'), bdd.to_expr(u)


def test_cpre_mealy_plus_one():
    cpre = fx.ue_preimage
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='env'),
                  y=dict(type='bool', owner='sys'))
    a.moore = False
    a.plus_one = True
    bdd = a.bdd
    # no env
    # y'
    a.action['env'] = ["True"]
    a.action['sys'] = ["y'"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = aut.add_expr('True')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.true
    target = aut.add_expr('False')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false
    target = aut.add_expr('y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.true
    target = aut.add_expr('! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false
    # y
    a.action['env'] = ["True"]
    a.action['sys'] = ["y"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = aut.add_expr('True')
    y =  bdd.add_expr('y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == y, bdd.to_expr(u)
    target = aut.add_expr('False')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false, bdd.to_expr(u)
    target = aut.add_expr('y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == y, bdd.to_expr(u)
    target = aut.add_expr('! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == y, bdd.to_expr(u)
    # with env
    # x => y'
    a.action['env'] = ["True"]
    a.action['sys'] = ["x => y'"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = aut.add_expr('y')
    y =  bdd.add_expr('y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.true, bdd.to_expr(u)
    target = aut.add_expr('! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.add_expr('! x'), bdd.to_expr(u)
    target = aut.add_expr('False')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false, bdd.to_expr(u)
    # x' => y'
    a.action['env'] = ["True"]
    a.action['sys'] = ["x' => y'"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = aut.add_expr('True')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.true, bdd.to_expr(u)
    target = aut.add_expr('y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.true, bdd.to_expr(u)
    target = aut.add_expr('! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false, bdd.to_expr(u)
    target = aut.add_expr('! x | y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.true, bdd.to_expr(u)
    # x' => y' with assumption
    a.action['env'] = ["! x'"]
    a.action['sys'] = ["x' => y'"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    # `plus_one` cannot depend on `x`
    target = aut.add_expr('! y')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.true, bdd.to_expr(u)
    # x => y' with assumption
    a.action['env'] = ["! x'"]
    a.action['sys'] = ["False"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = aut.add_expr('True')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false, bdd.to_expr(u)
    # x => y' with assumption
    a.action['env'] = ["x'"]
    a.action['sys'] = ["x'"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = aut.add_expr('True')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false, bdd.to_expr(u)
    #
    a.action['env'] = ["x'"]
    a.action['sys'] = ["True"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = aut.add_expr('True')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.true, bdd.to_expr(u)
    #
    a.action['env'] = ["x'"]
    a.action['sys'] = ["x & y"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = aut.add_expr('True')
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.add_expr('x & y'), bdd.to_expr(u)


def test_cpre_mealy_circular():
    cpre = fx.ue_preimage
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='env'),
                  y=dict(type='bool', owner='sys'))
    a.moore = False
    a.plus_one = False
    bdd = a.bdd
    #
    a.action['env'] = ["x'"]
    a.action['sys'] = ["x'"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = bdd.true
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.true
    #
    a.action['env'] = ["True"]
    a.action['sys'] = ["x'"]
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = bdd.true
    u = cpre(env_action, sys_action, target, aut)
    assert u == bdd.false


def test_ue_preimage():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='env'),
                  y=dict(type='bool', owner='sys'))
    a.action['env'] = ["True"]
    a.action['sys'] = ["x' => !y'"]
    symbolic.fill_blanks(a)
    a.moore = False
    a.plus_one = False
    aut = a.build()
    (env_action,) = aut.action['env']
    (sys_action,) = aut.action['sys']
    target = aut.add_expr('y')
    u = fx.ue_preimage(env_action, sys_action, target, aut)
    assert u == aut.bdd.false, aut.bdd.to_expr(u)
    aut.epvars = list(aut.uepvars)
    aut.upvars = list()
    u = fx.ue_preimage(env_action, sys_action, target, aut)
    assert u == aut.bdd.true, aut.bdd.to_expr(u)


if __name__ == '__main__':
    test_ue_preimage()
