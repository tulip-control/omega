"""Tests for `omega.games.gr1`."""
import logging
import pprint

from dd import mdd
from nose.tools import assert_raises

from omega.symbolic import symbolic, enumeration
from omega.games import gr1


log = logging.getLogger('astutils')
log.setLevel('ERROR')
log = logging.getLogger('omega')
log.setLevel('ERROR')


def test_streett_trivial_loop():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='sys'))
    symbolic.fill_blanks(a)
    with assert_raises(AssertionError):
        gr1.solve_streett_game(a)
    # solve
    a = a.build()
    assert len(a.win['<>[]']) == 1
    assert len(a.win['[]<>']) == 1
    z, yij, xijk = gr1.solve_streett_game(a)
    assert z == a.bdd.true, z
    # transducer
    t = gr1.make_streett_transducer(z, yij, xijk, a)
    assert isinstance(t, symbolic.Automaton), t
    # vars
    assert '_goal' in t.vars, t.vars
    vt = t.vars['_goal']['type']
    assert vt == 'int', vt
    dom = t.vars['_goal']['dom']
    assert dom == (0, 0), dom
    assert 'x' in t.vars, t.vars
    # init
    assert len(t.init['env']) == 1, t.init
    (init,) = t.init['env']
    init_ = t.add_expr('_goal = 0')
    assert init == init_, t.bdd.to_expr(init)
    # action
    assert len(t.action['sys']) == 1, t.action
    (action,) = t.action['sys']
    s = "(_goal = 0) & (_goal' = 0)"
    action_ = t.add_expr(s)
    assert action == action_, t.bdd.to_expr(action)
    # win
    assert len(t.win['[]<>']) == 0, t.win['[]<>']


def test_rabin_trivial_loop():
    a = symbolic.Automaton()
    a.acceptance = 'Rabin(1)'
    a.vars = dict(x=dict(type='bool', owner='sys'))
    symbolic.fill_blanks(a, rabin=True)
    with assert_raises(AssertionError):
        gr1.solve_rabin_game(a)
    # solve
    a = a.build()
    assert len(a.win['<>[]']) == 1
    assert len(a.win['[]<>']) == 1
    zk, yki, xkijr = gr1.solve_rabin_game(a)
    assert zk[-1] == a.bdd.true, zk
    # transducer
    t = gr1.make_rabin_transducer(zk, yki, xkijr, a)
    assert isinstance(t, symbolic.Automaton), t
    # vars
    assert '_goal' in t.vars, t.vars
    vt = t.vars['_goal']['type']
    assert vt == 'int', vt
    dom = t.vars['_goal']['dom']
    assert dom == (0, 0), dom
    assert '_hold' in t.vars, t.vars
    vt = t.vars['_hold']['type']
    assert vt == 'int', vt
    dom = t.vars['_hold']['dom']
    assert dom == (0, 1), dom
    assert 'x' in t.vars, t.vars
    # init
    assert len(t.init['env']) == 1, t.init
    (init,) = t.init['env']
    init_ = t.add_expr('(_goal = 0) & (_hold = 1)')
    assert init == init_, t.bdd.to_expr(init)
    # action
    assert len(t.action['sys']) == 1, t.action
    (action,) = t.action['sys']
    s = (
        "(_goal = 0) & (_goal' = 0) &"
        "(_hold' = 0)")
    action_ = t.add_expr(s)
    assert action == action_, t.bdd.to_expr(action)
    # win
    w = t.win['[]<>']
    assert len(w) == 0, w
    w = t.win['<>[]']
    assert len(w) == 0, w


def test_streett_deadend():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='int', dom=(0, 10), owner='sys'))
    a.action['sys'] = ["(x = 0) & (x' = 5)"]
    symbolic.fill_blanks(a)
    # solve
    aut = a.build()
    z, _, _ = gr1.solve_streett_game(aut)
    win_set = z
    assert win_set == aut.bdd.false, win_set


def test_rabin_deadend():
    a = symbolic.Automaton()
    a.acceptance = 'Rabin(1)'
    a.vars = dict(x=dict(type='int', dom=(0, 101), owner='sys'))
    a.action['sys'] = ["(x = 1) & (x' = 96 - x)"]
    symbolic.fill_blanks(a)
    aut = a.build()
    zk, _, _ = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.false, win_set


def test_streett_always_x():
    # always x
    a = symbolic.Automaton()
    a.moore = False
    a.vars = dict(x=dict(type='bool', owner='sys'))
    a.action['sys'] = ["x'"]
    symbolic.fill_blanks(a)
    # solve
    aut = a.build()
    z, yij, xijk = gr1.solve_streett_game(aut)
    assert z == aut.bdd.true, z
    # transducer
    t = gr1.make_streett_transducer(z, yij, xijk, aut)
    # init
    (init,) = t.init['env']
    init_ = t.add_expr('_goal = 0')
    assert init == init_, t.bdd.to_expr(init)
    # action
    (action,) = t.action['sys']
    s = (
        "(_goal = 0) & (_goal' = 0) & "
        "x' ")
    action_ = t.add_expr(s)
    assert action == action_, t.bdd.to_expr(action)
    #
    # always ! x
    a.init['env'] = ['!x']
    a.action['sys'] = ['!x']
    aut = a.build()
    # solve
    z, yij, xijk = gr1.solve_streett_game(aut)
    assert z == aut.add_expr('!x'), aut.bdd.to_expr(z)
    # tranducer
    t = gr1.make_streett_transducer(z, yij, xijk, aut)
    assert action_refined(aut, t)
    (init,) = t.init['env']
    init_ = t.add_expr('(_goal = 0) & !x')
    assert init == init_, t.bdd.to_expr(init)
    (action,) = t.action['sys']
    s = "(_goal = 0) & (_goal' = 0) & !x & !x'"
    action_ = t.add_expr(s)
    assert action == action_, t.bdd.to_expr(action)


def test_rabin_always_x():
    # always x
    a = symbolic.Automaton()
    a.acceptance = 'Rabin(1)'
    a.vars = dict(x=dict(type='bool', owner='sys'))
    a.action['sys'] = ["x'"]
    symbolic.fill_blanks(a, rabin=True)
    # solve
    aut = a.build()
    zk, yki, xkijr = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.true, win_set
    # transducer
    t = gr1.make_rabin_transducer(zk, yki, xkijr, aut)
    # init
    (init,) = t.init['env']
    s = '(_goal = 0) & (_hold = 1)'
    init_ = t.add_expr(s)
    assert init == init_, t.bdd.to_expr(init)
    # action
    (action,) = t.action['sys']
    s = (
        "(_goal = 0) & (_goal' = 0) & "
        "(_hold' = 0) & "
        "x' ")
    action_ = t.add_expr(s)
    assert action == action_, t.bdd.to_expr(action)
    #
    # always ! x
    a.init['env'] = ['!x']
    a.action['sys'] = ['!x']
    aut = a.build()
    # solve
    zk, yki, xkijr = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    win_set_ = aut.add_expr('!x')
    assert win_set == win_set_, aut.bdd.to_expr(win_set)
    # transducer
    t = gr1.make_rabin_transducer(zk, yki, xkijr, aut)
    assert action_refined(aut, t)
    (init,) = t.init['env']
    s = (
        '(_goal = 0) & (_hold = 1) & '
        '!x')
    init_ = t.add_expr(s)
    assert init == init_, t.bdd.to_expr(init)
    (action,) = t.action['sys']
    s = (
        "(_goal = 0) & (_goal' = 0) & "
        "(_hold' = 0) &"
        "!x & !x'")
    action_ = t.add_expr(s)
    assert action == action_, t.bdd.to_expr(action)


def test_streett_counter():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='sys'))
    a.action['sys'] = ["x => !x'"]
    a.win['[]<>'] = ['x']
    symbolic.fill_blanks(a)
    # solve
    aut = a.build()
    z, yij, xijk = gr1.solve_streett_game(aut)
    assert z == aut.bdd.true, z
    # transducer
    t = gr1.make_streett_transducer(z, yij, xijk, aut)
    (init,) = t.init['env']
    init_ = t.add_expr('_goal = 0')
    assert init == init_, t.bdd.to_expr(init)
    (action,) = t.action['sys']
    assert action_refined(aut, t)
    # regression
    s = (
        "(_goal = 0) & (_goal' = 0) & "
        "(x <-> !x')")
    action_ = t.add_expr(s)
    assert action == action_, t.bdd.to_expr(action)


def test_rabin_counter():
    a = symbolic.Automaton()
    a.plus_one = False
    a.qinit = '\A \A'
    a.vars = dict(x=dict(type='bool', owner='sys'))
    a.action['sys'] = ["x => !x'"]
    a.win['[]<>'] = ['x']
    symbolic.fill_blanks(a, rabin=True)
    # solve
    aut = a.build()
    zk, yki, xkijr = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.true, aut.bdd.to_expr(win_set)
    # transducer
    t = gr1.make_rabin_transducer(zk, yki, xkijr, aut)
    assert action_refined(aut, t)
    (init,) = t.init['env']
    s = '(_goal = 0) & (_hold = 1)'
    init_ = t.add_expr(s)
    assert init == init_, t.bdd.to_expr(init)
    (action,) = t.action['sys']
    # regression
    s = (
        "(_goal = 0) & (_goal' = 0) & "
        "(_hold' = 0) & "
        "ite(_hold = 0, x <-> !x', x => !x')")
    action_ = t.add_expr(s)
    assert action == action_, t.bdd.to_expr(action)


def test_rabin_persistence():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='sys'))
    a.init['env'] = ['!x']
    a.win['<>[]'] = ['x']
    symbolic.fill_blanks(a, rabin=True)
    # solve
    aut = a.build()
    zk, yki, xkijr = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.true, aut.bdd.to_expr(win_set)
    # tranducer
    t = gr1.make_rabin_transducer(zk, yki, xkijr, aut)
    assert action_refined(aut, t)
    (init,) = t.init['env']
    s = '(_goal = 0) & (_hold = 1) & !x'
    init_ = t.add_expr(s)
    assert init == init_, t.bdd.to_expr(init)
    (action,) = t.action['sys']
    s = (
        "(_goal = 0) & (_goal' = 0) & "
        "ite(_hold' = 1, !x & x', x & x')")
    action_ = t.add_expr(s)
    assert action == action_, t.bdd.to_expr(action)
    #
    # unrealizable
    a.win['[]<>'] = ['!x']
    aut = a.build()
    zk, _, _ = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.false, aut.bdd.to_expr(win_set)


def test_rabin_persistence_2():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='sys'))
    a.init['sys'] = []
    a.win['<>[]'] = ['x', '!x']
    symbolic.fill_blanks(a, rabin=True)
    # solve
    aut = a.build()
    zk, yki, xkijr = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.true, aut.bdd.to_expr(win_set)
    # transducer
    t = gr1.make_rabin_transducer(zk, yki, xkijr, aut)
    assert action_refined(aut, t)
    (init,) = t.init['env']
    s = '(_goal = 0) & (_hold = 2)'
    init_ = t.add_expr(s)
    assert init == init_, t.bdd.to_expr(init)
    (action,) = t.action['sys']
    # enumeration.dump_relation(action, t)
    s = (
        "(_goal = 0) & (_goal' = 0) & "
        "ite(_hold = 1,"
        "(_hold' = 1) & !x',"
        "ite(_hold = 0,"
        "(_hold' = 0) & x',"
        "(_hold = 2) & ("
        "( (_hold' = 0) & x' ) | "
        "( (_hold' = 1) & !x' )"
        ") ) )")
    action_ = t.add_expr(s)
    assert action == action_, t.bdd.to_expr(action)


def test_streett_with_safety_assumption():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='env'))
    a.moore = False
    a.plus_one = False
    a.action['env'] = ['x']
    a.action['sys'] = ['x']
    symbolic.fill_blanks(a)
    # solve
    aut = a.build()
    z, yij, xijk = gr1.solve_streett_game(aut)
    assert z == aut.bdd.true, z
    # transducer
    t = gr1.make_streett_transducer(z, yij, xijk, aut)
    (init,) = t.init['env']
    assert init == t.add_expr('_goal = 0'), t.bdd.to_expr(init)
    (action,) = t.action['sys']
    action_ = t.add_expr("x => ((_goal = 0) & (_goal' = 0))")
    assert action == action_, t.bdd.to_expr(action)
    #
    # negate action to make unrealizable
    a.action['sys'] = ['!x']
    # solve
    aut = a.build()
    z, yij, xijk = gr1.solve_streett_game(aut)
    assert z == aut.add_expr('!x'), aut.bdd.to_expr(z)
    # transducer
    with assert_raises(AssertionError):
        gr1.make_streett_transducer(z, yij, xijk, aut)
    # Moore case
    a.moore = True
    a.plus_one = False
    a.action['env'] = ['x']
    a.action['sys'] = ['x']
    # solve
    aut = a.build()
    z_moore, yij, xijk = gr1.solve_streett_game(aut)
    assert z_moore != z, 'should differ due to plus_one'
    t = gr1.make_streett_transducer(z_moore, yij, xijk, aut)
    (init,) = t.init['env']
    assert init == t.add_expr('_goal = 0'), t.bdd.to_expr(init)


def test_rabin_with_safety_assumption():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='env'))
    a.init['env'] = ['x']
    a.action['env'] = ["x'"]
    a.action['sys'] = ["x"]
    symbolic.fill_blanks(a, rabin=True)
    # solve
    aut = a.build()
    zk, yki, xkijr = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.add_expr('x'), win_set
    # transducer
    t = gr1.make_rabin_transducer(zk, yki, xkijr, aut)
    assert action_refined(aut, t)
    (init,) = t.init['env']
    s = 'x & (_goal = 0) & (_hold = 1)'
    init_ = t.add_expr(s)
    assert init == init_, t.bdd.to_expr(init)
    (action,) = t.action['sys']
    s = "((_goal = 0) & (_goal' = 0) & (_hold' = 0) & x)"
    action_ = t.add_expr(s)
    assert action == action_, t.bdd.to_expr(action)
    #
    # negate action to make unrealizable
    a.action['sys'] = ['!x']
    # solve
    aut = a.build()
    zk, yki, xkijr = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == t.bdd.false, t.bdd.to_expr(win_set)
    with assert_raises(AssertionError):
        gr1.make_rabin_transducer(zk, yki, xkijr, aut)


def test_streett_with_liveness_assumption():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='env'),
                  y=dict(type='int', dom=(0, 2), owner='sys'))
    a.init['env'] = ['y < 2']
    a.action['sys'] = [
        "((y = 0) & !x) => (y' = 0)",
        "(y = 0) => (y' < 2)",
        "(y = 1) => (y' = 0)",
        "(y = 2) => False"]
    a.win['<>[]'] = ['!x']
    a.win['[]<>'] = ['y = 1']
    symbolic.fill_blanks(a)
    aut = a.build()
    # solve
    z, yij, xijk = gr1.solve_streett_game(aut)
    z_ = aut.add_expr('y < 2')
    e = aut.bdd.to_expr(z)
    e_ = aut.bdd.to_expr(z_)
    assert z == z_, (e, e_)
    # transducer
    t = gr1.make_streett_transducer(z, yij, xijk, aut)
    assert action_refined(aut, t)
    (init,) = t.init['env']
    assert init == t.add_expr('(y < 2) & (_goal = 0)'), t.bdd.to_expr(init)
    (action,) = t.action['sys']
    s = (
        "( (y = 0) => ite(x, (y' = 1), (y' = 0)) ) & "
        "( (y = 1) => (y' = 0) ) & "
        "( (_goal = 0) & (_goal' = 0) ) & "
        "( (y != 2) & (y != 3) )")
    action_ = t.add_expr(s)
    sat = list(t.bdd.sat_iter(action))
    sys_action = aut.action['sys'][0]
    sys_action = gr1._copy_bdd(sys_action, aut.bdd, t.bdd)
    u = t.bdd.apply('->', action, sys_action)
    assert u == t.bdd.true, u
    assert action == action_, (action, action_, pprint.pprint(sat))
    #
    # test complement
    b = symbolic.Automaton()
    b.acceptance = 'Rabin(1)'
    b.vars = dict(x=dict(type='bool', owner='sys'),
                  y=dict(type='int', dom=(0, 2), owner='env'))
    b.action['env'] = a.action['sys']
    b.win['<>[]'] = ['y != 1']
    b.win['[]<>'] = ['x']
    symbolic.fill_blanks(b, rabin=True)
    aut_rabin = b.build()
    zk, yki, xkijr = gr1.solve_rabin_game(aut_rabin)
    rabin_win_set = zk[-1]
    bdd = aut_rabin.bdd
    streett_win_set = gr1._copy_bdd(z, aut.bdd, bdd)
    assert rabin_win_set == bdd.apply('not', streett_win_set)
    with assert_raises(AssertionError):
        gr1.make_rabin_transducer(zk, yki, xkijr, aut_rabin)


def test_streett_2_goals():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='sys'))
    a.win['[]<>'] = ['x', '!x']
    symbolic.fill_blanks(a)
    aut = a.build()
    # solve
    z, yij, xijk = gr1.solve_streett_game(aut)
    assert z == aut.bdd.true, aut.bdd.to_expr(z)
    # transducer
    t = gr1.make_streett_transducer(z, yij, xijk, aut)
    assert action_refined(aut, t)
    (action,) = t.action['sys']
    # print_fol_bdd(action, t.bdd, t.vars)
    # enumeration.dump_relation(action, t)
    s = (
        "((x & (_goal = 0)) => (_goal' = 1)) & "
        "((!x & (_goal = 1)) => (_goal' = 0)) & "
        "((!x & (_goal = 0)) => (x' & (_goal' = 0))) & "
        "((x & (_goal = 1)) => (!x' & (_goal' = 1)))")
    action_ = t.add_expr(s)
    assert action == action_, t.bdd.to_expr(action)


def test_rabin_goal():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='env'))
    a.win['[]<>'] = ['x']
    symbolic.fill_blanks(a, rabin=True)
    aut = a.build()
    # solve
    zk, yki, xkijr = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.false, aut.bdd.to_expr(win_set)


def test_rabin_2_goals():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='env'),
                  y=dict(type='bool', owner='sys'))
    a.win['[]<>'] = ['x => y']
    symbolic.fill_blanks(a, rabin=True)
    aut = a.build()
    # solve
    zk, _, _ = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.true, aut.bdd.to_expr(win_set)
    #
    # unrealizable
    a.win['<>[]'] = ['! y']
    aut = a.build()
    zk, _, _ = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.false, aut.bdd.to_expr(win_set)
    #
    # realizable again
    a.win['<>[]'] = ['y']
    aut = a.build()
    zk, _, _ = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.true, aut.bdd.to_expr(win_set)
    #
    # unrealizable
    a.win['[]<>'] = ['x => y', '!y']
    aut = a.build()
    zk, _, _ = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.false, aut.bdd.to_expr(win_set)


def test_is_realizable():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='env'),
                  y=dict(type='int', dom=(0, 5), owner='sys'))
    # \A \A realizable
    a.init['env'] = ['x & (y = 1)']
    a.init['sys'] = ['(y < 3)']
    a.qinit = '\A \A'
    aut = a.build()
    z = aut.add_expr('x & (y < 2)')
    assert gr1.is_realizable(z, aut)
    # \A \A unrealizable
    a.init['sys'] = ['(y < 1)']
    aut = a.build()
    assert not gr1.is_realizable(z, aut)
    # \E \E realizable
    a.init['env'] = ['x & (y = 1)']
    a.init['sys'] = ['(y < 3)']
    a.qinit = '\E \E'
    aut = a.build()
    z = aut.add_expr('x & (y < 2)')
    assert gr1.is_realizable(z, aut)
    # \E \E unrealizable
    a.init['env'] = ['x & (y = 1)']
    a.init['sys'] = ['(y > 10)']
    a.qinit = '\E \E'
    aut = a.build()
    z = aut.add_expr('True')
    assert not gr1.is_realizable(z, aut)
    # \A \E realizable
    a.moore = False
    a.init['env'] = ['True']
    s = (
        '(x => (y = 1)) & '
        '((! x) => (y = 4))')
    a.init['sys'] = [s]
    a.qinit = '\A \E'
    aut = a.build()
    z = aut.add_expr('y > 0')
    assert gr1.is_realizable(z, aut)
    # \A \E unrealizable
    s = (
        '(x => (y = 1)) & '
        '((! x) => (y = 10))')
    a.init['sys'] = [s]
    a.qinit = '\A \E'
    aut = a.build()
    z = aut.add_expr('True')
    assert not gr1.is_realizable(z, aut)
    # \E \A realizable
    a.moore = True
    s = 'x => (y = 1)'
    a.init['sys'] = [s]
    a.qinit = '\E \A'
    aut = a.build()
    z = aut.add_expr('y <= 2')
    assert gr1.is_realizable(z, aut)
    # \E \A unrealizable
    s = (
        '(x => (y = 1)) & '
        '((! x) => (y = 3))')
    a.init['sys'] = [s]
    a.qinit = '\E \A'
    aut = a.build()
    z = aut.add_expr('True')
    assert not gr1.is_realizable(z, aut)


def test_make_init():
    t = symbolic.Automaton()
    t.vars['x'] = dict(type='bool', owner='sys')
    t = t.build()
    aut = t
    internal_init = aut.bdd.true
    win = aut.bdd.true
    aut.qinit = '???'
    with assert_raises(ValueError):
        gr1._make_init(internal_init, win, t, aut)


def test_streett_qinit_exist_forall():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='env'),
                  y=dict(type='int', dom=(0, 5), owner='sys'))
    a.moore = True
    a.qinit = '\E \A'
    a.init['env'] = ['x']
    a.init['sys'] = ['x -> (y = 4)']
    symbolic.fill_blanks(a)
    # solve
    a = a.build()
    z, yij, xijk = gr1.solve_streett_game(a)
    assert z == a.add_expr('(y >= 0) & (y <= 5)'), z
    # transducer
    t = gr1.make_streett_transducer(z, yij, xijk, a)
    u = t.init['env'][0]
    u_ = t.add_expr('x & (y = 4) & (_goal = 0)')
    assert u == u_, t.bdd.to_expr(u)


def test_trivial_winning_set():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='sys'))
    a.win['<>[]'] = ['!x']
    symbolic.fill_blanks(a)
    triv, aut = gr1.trivial_winning_set(a)
    assert triv == aut.bdd.true, aut.bdd.to_expr(triv)


def test_warn_moore_mealy():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='env'),
                  y=dict(type='int', dom=(0, 25), owner='sys'))
    # Moore OK
    a.moore = True
    a.action['env'] = ["x & x'"]
    a.action['sys'] = ["(y > 4) & (y' = 5)"]
    symbolic.fill_blanks(a)
    aut = a.build()
    r = gr1._warn_moore_mealy(aut)
    assert r is True, r
    # Moore with env' in sys action
    a.action['env'] = ["x & x'"]
    a.action['sys'] = ["x' & (y > 4) & (y' = 5)"]
    aut = a.build()
    r = gr1._warn_moore_mealy(aut)
    assert r is False, r
    # Mealy with env' in sys action
    a.moore = False
    aut = a.build()
    r = gr1._warn_moore_mealy(aut)
    assert r is True, r
    # Mealy with sys' in env action
    a.action['env'] = ["x & x' & (y' > 4)"]
    a.moore = False
    aut = a.build()
    r = gr1._warn_moore_mealy(aut)
    assert r is False, r
    # Moore with sys' in env action
    a.action['sys'] = ["(y > 4) & (y' = 5)"]
    a.moore = True
    aut = a.build()
    r = gr1._warn_moore_mealy(aut)
    assert r is False, r


def action_refined(aut_a, aut_b):
    """Return `True` if action of `aut_b` refines `aut_a`.

    @type aut_a, aut_b: `symbolic.Automaton`
    """
    assert aut_a.moore == aut_b.moore, (
        aut_a.moore, aut_b.moore)
    assert aut_a.plus_one == aut_b.plus_one, (
        aut_a.plus_one, aut_b.plus_one)
    assert aut_a.bdd is aut_b.bdd
    bdd = aut_a.bdd
    (a,) = aut_a.action['sys']
    (b,) = aut_b.action['sys']
    refined = bdd.apply('->', b, a)
    return refined == bdd.true


def print_fol_bdd(u, bdd, table):
    """Print a first-order formula for node `u`.

    Example:

    ```
    t = symbolic.Automaton()
    t.vars = dict(x=dict(type='int', dom=(0, 5), owner='sys'))
    t.action['sys'] = ['x = 1']
    u = t.action['sys'][0]
    print_fol_bdd(u, t.bdd, t.vars)
    ```
    """
    bdd.incref(u)
    dvars = symbolic._prime_and_order_table(table)
    m, umap = mdd.bdd_to_mdd(bdd, dvars)
    u_ = -umap[abs(u)]
    s = m.to_expr(u_)
    print(s)


if __name__ == '__main__':
    test_rabin_2_goals()
