"""Tests for `omega.games.gr1`."""
import logging
import pprint

from dd import mdd
from nose.tools import assert_raises

from omega.symbolic import enumeration
from omega.symbolic import symbolic
from omega.symbolic import temporal as trl
from omega.games import gr1


log = logging.getLogger('astutils')
log.setLevel('ERROR')
log = logging.getLogger('omega')
log.setLevel('ERROR')


def test_streett_trivial_loop():
    a = trl.default_streett_automaton()
    a.declare_variables(x='bool')
    a.varlist['sys'] = ['x']
    # solve
    assert len(a.win['<>[]']) == 1
    assert len(a.win['[]<>']) == 1
    z, yij, xijk = gr1.solve_streett_game(a)
    assert z == a.bdd.true, z
    # transducer
    gr1.make_streett_transducer(z, yij, xijk, a)
    # vars
    assert '_goal' in a.vars, a.vars
    vt = a.vars['_goal']['type']
    assert vt == 'int', vt
    dom = a.vars['_goal']['dom']
    assert dom == (0, 0), dom
    assert 'x' in a.vars, a.vars
    # init
    init = a.init['impl']
    init_ = a.add_expr('_goal = 0')
    assert init == init_, a.bdd.to_expr(init)
    # action
    action = a.action['impl']
    s = "(_goal = 0) /\ (_goal' = 0)"
    action_ = a.add_expr(s)
    assert action == action_, a.bdd.to_expr(action)


def test_rabin_trivial_loop():
    a = trl.default_rabin_automaton()
    a.acceptance = 'Rabin(1)'
    a.declare_variables(x='bool')
    a.varlist['sys'] = ['x']
    # solve
    assert len(a.win['<>[]']) == 1
    assert len(a.win['[]<>']) == 1
    zk, yki, xkijr = gr1.solve_rabin_game(a)
    assert zk[-1] == a.bdd.true, zk
    # transducer
    gr1.make_rabin_transducer(zk, yki, xkijr, a)
    # vars
    assert '_goal' in a.vars, a.vars
    vt = a.vars['_goal']['type']
    assert vt == 'int', vt
    dom = a.vars['_goal']['dom']
    assert dom == (0, 0), dom
    assert '_hold' in a.vars, a.vars
    vt = a.vars['_hold']['type']
    assert vt == 'int', vt
    dom = a.vars['_hold']['dom']
    assert dom == (0, 1), dom
    assert 'x' in a.vars, a.vars
    # init
    init = a.init['impl']
    init_ = a.add_expr('(_goal = 0) /\ (_hold = 1)')
    assert init == init_, a.bdd.to_expr(init)
    # action
    action = a.action['impl']
    s = (
        "(_goal = 0) /\ (_goal' = 0) /\ "
        "(_hold' = 0)")
    action_ = a.add_expr(s)
    assert action == action_, a.bdd.to_expr(action)


def test_streett_deadend():
    aut = trl.default_streett_automaton()
    aut.declare_variables(x=(0, 10))
    aut.varlist['sys'] = ['x']
    aut.action['sys'] = aut.add_expr("(x = 0) /\ (x' = 5)")
    z, _, _ = gr1.solve_streett_game(aut)
    win_set = z
    assert win_set == aut.bdd.false, win_set


def test_rabin_deadend():
    aut = trl.default_streett_automaton()
    aut.acceptance = 'Rabin(1)'
    aut.declare_variables(x=(0, 101))
    aut.varlist['sys'] = ['x']
    aut.action['sys'] = aut.add_expr("(x = 1) /\ (x' = 96 - x)")
    zk, _, _ = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.false, win_set


def test_streett_always_x():
    # always x
    aut = trl.default_streett_automaton()
    aut.declare_variables(x='bool')
    aut.varlist['sys'] = ['x']
    aut.moore = False
    aut.action['sys'] = aut.add_expr("x' ")
    # solve
    z, yij, xijk = gr1.solve_streett_game(aut)
    assert z == aut.true, z
    # transducer
    gr1.make_streett_transducer(z, yij, xijk, aut)
    # init
    init = aut.init['impl']
    init_ = aut.add_expr('_goal = 0')
    assert init == init_, aut.bdd.to_expr(init)
    # action
    action = aut.action['impl']
    s = (
        "(_goal = 0) /\ (_goal' = 0) /\ "
        "x' ")
    action_ = aut.add_expr(s)
    assert action == action_, aut.bdd.to_expr(action)
    #
    # always ~ x
    aut.init['env'] = aut.add_expr(' ~ x')
    aut.action['sys'] = aut.add_expr(' ~ x')
    # solve
    z, yij, xijk = gr1.solve_streett_game(aut)
    assert z == aut.add_expr(' ~ x'), aut.bdd.to_expr(z)
    # tranducer
    gr1.make_streett_transducer(z, yij, xijk, aut)
    assert action_refined(aut)
    init = aut.init['impl']
    init_ = aut.add_expr('(_goal = 0)')
    assert init == init_, aut.bdd.to_expr(init)
    action = aut.action['impl']
    s = "(_goal = 0) /\ (_goal' = 0) /\ ~ x /\ ~ x'"
    action_ = aut.add_expr(s)
    assert action == action_, aut.bdd.to_expr(action)


def test_rabin_always_x():
    # always x
    aut = trl.default_rabin_automaton()
    aut.declare_variables(x='bool')
    aut.varlist['sys'] = ['x']
    aut.acceptance = 'Rabin(1)'
    aut.action['sys'] = aut.add_expr("x' ")
    # solve
    zk, yki, xkijr = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.true, win_set
    # transducer
    gr1.make_rabin_transducer(zk, yki, xkijr, aut)
    # init
    init = aut.init['impl']
    s = '(_goal = 0) /\ (_hold = 1)'
    init_ = aut.add_expr(s)
    assert init == init_, aut.bdd.to_expr(init)
    # action
    action = aut.action['impl']
    s = (
        "(_goal = 0) /\ (_goal' = 0) /\ "
        "(_hold' = 0) /\ "
        "x' ")
    action_ = aut.add_expr(s)
    assert action == action_, aut.bdd.to_expr(action)
    #
    # always ~ x
    aut.init['env'] = aut.add_expr(' ~ x')
    aut.action['sys'] = aut.add_expr(' ~ x')
    # solve
    zk, yki, xkijr = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    win_set_ = aut.add_expr(' ~ x')
    assert win_set == win_set_, aut.bdd.to_expr(win_set)
    # transducer
    gr1.make_rabin_transducer(zk, yki, xkijr, aut)
    assert action_refined(aut)
    init = aut.init['impl']
    s = ' (_goal = 0) /\ (_hold = 1) '
    init_ = aut.add_expr(s)
    assert init == init_, aut.bdd.to_expr(init)
    action = aut.action['impl']
    s = (
        "(_goal = 0) /\ (_goal' = 0) /\ "
        "(_hold' = 0) /\ "
        " ~ x /\ ~ x'")
    action_ = aut.add_expr(s)
    assert action == action_, aut.bdd.to_expr(action)


def test_streett_counter():
    aut = trl.default_streett_automaton()
    aut.declare_variables(x='bool')
    aut.varlist['sys'] = ['x']
    aut.action['sys'] = aut.add_expr("x => ~ x' ")
    aut.win['[]<>'] = [aut.add_expr('x')]
    # solve
    z, yij, xijk = gr1.solve_streett_game(aut)
    assert z == aut.true, z
    # transducer
    gr1.make_streett_transducer(z, yij, xijk, aut)
    init = aut.init['impl']
    init_ = aut.add_expr('_goal = 0')
    assert init == init_, aut.bdd.to_expr(init)
    action = aut.action['impl']
    assert action_refined(aut)
    # regression
    s = (
        "(_goal = 0) /\ (_goal' = 0) /\ "
        "(x <=> ~ x')")
    action_ = aut.add_expr(s)
    assert action == action_, aut.bdd.to_expr(action)


def test_rabin_counter():
    aut = trl.default_rabin_automaton()
    aut.declare_variables(x='bool')
    aut.varlist['sys'] = ['x']
    aut.plus_one = False
    aut.qinit = '\A \A'
    aut.action['sys'] = aut.add_expr("x => ~ x' ")
    aut.win['[]<>'] = [aut.add_expr('x')]
    # solve
    zk, yki, xkijr = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.true, aut.bdd.to_expr(win_set)
    # transducer
    gr1.make_rabin_transducer(zk, yki, xkijr, aut)
    assert action_refined(aut)
    init = aut.init['impl']
    s = '(_goal = 0) /\ (_hold = 1)'
    init_ = aut.add_expr(s)
    assert init == init_, aut.bdd.to_expr(init)
    action = aut.action['impl']
    # regression
    s = (
        "(_goal = 0) /\ (_goal' = 0) /\ "
        "(_hold' = 0) /\ "
        "ite(_hold = 0, x <=> ~ x', x => ~ x')")
    action_ = aut.add_expr(s)
    assert action == action_, aut.bdd.to_expr(action)


def test_rabin_persistence():
    aut = trl.default_rabin_automaton()
    aut.declare_variables(x='bool')
    aut.varlist['sys'] = ['x']
    aut.init['sys'] = aut.add_expr(' ~ x')
    aut.win['<>[]'] = [aut.add_expr('x')]
    # solve
    zk, yki, xkijr = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.true, aut.bdd.to_expr(win_set)
    # tranducer
    gr1.make_rabin_transducer(zk, yki, xkijr, aut)
    assert action_refined(aut)
    init = aut.init['impl']
    s = '(_goal = 0) /\ (_hold = 1) /\ ~ x'
    init_ = aut.add_expr(s)
    assert init == init_, aut.bdd.to_expr(init)
    action = aut.action['impl']
    s = (
        "(_goal = 0) /\ (_goal' = 0) /\ "
        "ite(_hold' = 1, ~ x /\ x', x /\ x')")
    action_ = aut.add_expr(s)
    assert action == action_, aut.bdd.to_expr(action)
    #
    # unrealizable
    aut.win['[]<>'] = [aut.add_expr(' ~ x')]
    zk, _, _ = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.false, aut.bdd.to_expr(win_set)


def test_rabin_persistence_2():
    aut = trl.default_rabin_automaton()
    aut.declare_variables(x='bool')
    aut.varlist['sys'] = ['x']
    aut.init['sys'] = aut.true
    aut.win['<>[]'] = [aut.add_expr('x'), aut.add_expr(' ~ x')]
    # solve
    zk, yki, xkijr = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.true, aut.bdd.to_expr(win_set)
    # transducer
    gr1.make_rabin_transducer(zk, yki, xkijr, aut)
    assert action_refined(aut)
    init = aut.init['impl']
    s = '(_goal = 0) /\ (_hold = 2)'
    init_ = aut.add_expr(s)
    assert init == init_, aut.bdd.to_expr(init)
    action = aut.action['impl']
    # enumeration.dump_relation(action, aut)
    s = (
        "(_goal = 0) /\ (_goal' = 0) /\ "
        "ite(_hold = 1,"
        "(_hold' = 1) /\ ~ x',"
        "ite(_hold = 0,"
        "(_hold' = 0) /\ x',"
        "(_hold = 2) /\ ("
        "( (_hold' = 0) /\ x' ) \/ "
        "( (_hold' = 1) /\ ~ x' )"
        ") ) )")
    action_ = aut.add_expr(s)
    assert action == action_, aut.bdd.to_expr(action)


def test_streett_with_safety_assumption():
    aut = trl.default_streett_automaton()
    aut.declare_variables(x='bool')
    aut.varlist['env'] = ['x']
    aut.moore = False
    aut.plus_one = False
    aut.action['env'] = aut.add_expr('x')
    aut.action['sys'] = aut.add_expr('x')
    # solve
    z, yij, xijk = gr1.solve_streett_game(aut)
    assert z == aut.true, z
    # transducer
    gr1.make_streett_transducer(z, yij, xijk, aut)
    init = aut.init['impl']
    assert init == aut.add_expr('_goal = 0'), aut.bdd.to_expr(init)
    action = aut.action['impl']
    action_ = aut.add_expr("x => ((_goal = 0) /\ (_goal' = 0))")
    assert action == action_, aut.bdd.to_expr(action)
    #
    # negate action to make unrealizable
    aut.action['sys'] = aut.add_expr(' ~ x')
    # solve
    z, yij, xijk = gr1.solve_streett_game(aut)
    assert z == aut.add_expr(' ~ x'), aut.bdd.to_expr(z)
    # transducer
    with assert_raises(AssertionError):
        gr1.make_streett_transducer(z, yij, xijk, aut)
    # Moore case
    aut.moore = True
    aut.plus_one = False
    aut.action['env'] = aut.add_expr('x')
    aut.action['sys'] = aut.add_expr('x')
    # solve
    z_moore, yij, xijk = gr1.solve_streett_game(aut)
    assert z_moore != z, 'should differ due to plus_one'
    gr1.make_streett_transducer(z_moore, yij, xijk, aut)
    init = aut.init['impl']
    assert init == aut.add_expr('_goal = 0'), aut.bdd.to_expr(init)


def test_rabin_with_safety_assumption():
    aut = trl.default_rabin_automaton()
    aut.declare_variables(x='bool')
    aut.varlist['env'] = ['x']
    aut.init['env'] = aut.add_expr('x')
    aut.action['env'] = aut.add_expr("x' ")
    aut.action['sys'] = aut.add_expr("x")
    # solve
    zk, yki, xkijr = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.add_expr('x'), win_set
    # transducer
    gr1.make_rabin_transducer(zk, yki, xkijr, aut)
    assert action_refined(aut)
    init = aut.init['impl']
    s = '(_goal = 0) /\ (_hold = 1)'
    init_ = aut.add_expr(s)
    assert init == init_, aut.bdd.to_expr(init)
    action = aut.action['impl']
    s = "((_goal = 0) /\ (_goal' = 0) /\ (_hold' = 0) /\ x)"
    action_ = aut.add_expr(s)
    assert action == action_, aut.bdd.to_expr(action)
    #
    # negate action to make unrealizable
    aut.action['sys'] = aut.add_expr(' ~ x')
    # solve
    zk, yki, xkijr = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.false, aut.bdd.to_expr(win_set)
    with assert_raises(AssertionError):
        gr1.make_rabin_transducer(zk, yki, xkijr, aut)


def test_streett_with_liveness_assumption():
    aut = trl.default_streett_automaton()
    aut.declare_variables(x='bool', y=(0, 2))
    aut.varlist = dict(env=['x'], sys=['y'])
    aut.init['sys'] = aut.add_expr(' y \in 0..2 ')
    aut.action['sys'] = aut.add_expr(
        """
        /\ ( ((y = 0) /\ ~ x) => (y' = 0) )
        /\ ((y = 0) => (y' < 2))
        /\ ((y = 1) => (y' = 0))
        /\ ((y = 2) => FALSE)
        /\ y \in 0..2
        """)
    aut.win['<>[]'] = [aut.add_expr(' ~ x')]
    aut.win['[]<>'] = [aut.add_expr('y = 1')]
    # solve
    z, yij, xijk = gr1.solve_streett_game(aut)
    z_ = aut.add_expr('y < 2')
    e = aut.bdd.to_expr(z)
    e_ = aut.bdd.to_expr(z_)
    assert z == z_, (e, e_)
    # transducer
    gr1.make_streett_transducer(z, yij, xijk, aut)
    assert action_refined(aut)
    init = aut.init['impl']
    assert init == aut.add_expr('(y < 2) /\ (_goal = 0)'), aut.bdd.to_expr(init)
    action = aut.action['impl']
    s = (
        "( (y = 0) => ite(x, (y' = 1), (y' = 0)) ) /\ "
        "( (y = 1) => (y' = 0) ) /\ "
        "( (_goal = 0) /\ (_goal' = 0) ) /\ "
        "( (y /= 2) /\ (y /= 3) )")
    action_ = aut.add_expr(s)
    sat = list(aut.bdd.pick_iter(action))
    sys_action = aut.action['sys']
    sys_action = gr1._copy_bdd(sys_action, aut.bdd, aut.bdd)
    u = aut.apply('=>', action, sys_action)
    assert u == aut.bdd.true, u
    assert action == action_, (action, action_, pprint.pprint(sat))
    #
    # test complement
    b = trl.default_rabin_automaton()
    b.acceptance = 'Rabin(1)'
    b.declare_variables(x='bool', y=(0, 2))
    b.varlist = dict(env=['y'], sys=['x'])
    b.action['env'] = gr1._copy_bdd(aut.action['sys'], aut.bdd, b.bdd)
    b.win['<>[]'] = [b.add_expr('y /= 1')]
    b.win['[]<>'] = [b.add_expr('x')]
    zk, yki, xkijr = gr1.solve_rabin_game(b)
    rabin_win_set = zk[-1]
    bdd = b.bdd
    streett_win_set = gr1._copy_bdd(z, aut.bdd, bdd)
    assert rabin_win_set == bdd.apply('not', streett_win_set)
    with assert_raises(AssertionError):
        gr1.make_rabin_transducer(zk, yki, xkijr, b)


def test_streett_2_goals():
    aut = trl.default_streett_automaton()
    aut.declare_variables(x='bool')
    aut.varlist = dict(env=list(), sys=['x'])
    aut.win['[]<>'] = [aut.add_expr('x'), aut.add_expr(' ~ x')]
    # solve
    z, yij, xijk = gr1.solve_streett_game(aut)
    assert z == aut.bdd.true, aut.bdd.to_expr(z)
    # transducer
    gr1.make_streett_transducer(z, yij, xijk, aut)
    assert action_refined(aut)
    action = aut.action['impl']
    # print_fol_bdd(action, aut.bdd, aut.vars)
    # enumeration.dump_relation(action, aut)
    s = (
        "((x /\ (_goal = 0)) => (_goal' = 1)) /\ "
        "(( ~ x /\ (_goal = 1)) => (_goal' = 0)) /\ "
        "(( ~ x /\ (_goal = 0)) => (x' /\ (_goal' = 0))) /\ "
        "((x /\ (_goal = 1)) => ( ~ x' /\ (_goal' = 1)))")
    action_ = aut.add_expr(s)
    assert action == action_, aut.bdd.to_expr(action)


def test_rabin_goal():
    aut = trl.default_rabin_automaton()
    aut.declare_variables(x='bool')
    aut.varlist = dict(env=['x'], sys=list())
    aut.win['[]<>'] = [aut.add_expr('x')]
    # solve
    zk, yki, xkijr = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.false, aut.bdd.to_expr(win_set)


def test_rabin_2_goals():
    aut = trl.default_rabin_automaton()
    aut.declare_variables(x='bool', y='bool')
    aut.varlist = dict(env=['x'], sys=['y'])
    aut.win['[]<>'] = [aut.add_expr('x => y')]
    # solve
    zk, _, _ = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.true, aut.bdd.to_expr(win_set)
    #
    # unrealizable
    aut.win['<>[]'] = [aut.add_expr(' ~ y')]
    zk, _, _ = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.false, aut.bdd.to_expr(win_set)
    #
    # realizable again
    aut.win['<>[]'] = [aut.add_expr('y')]
    zk, _, _ = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.true, aut.bdd.to_expr(win_set)
    #
    # unrealizable
    aut.win['[]<>'] = [aut.add_expr(s) for s in ['x => y', ' ~ y']]
    zk, _, _ = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.false, aut.bdd.to_expr(win_set)


def test_is_realizable():
    aut = trl.default_streett_automaton()
    aut.declare_variables(x='bool', y=(0, 5))
    aut.varlist = dict(env=['x'], sys=['y'])
    aut.prime_varlists()
    # \A \A realizable
    aut.init['env'] = aut.add_expr('x /\ (y = 1)')
    aut.init['sys'] = aut.true
    aut.qinit = '\A \A'
    z = aut.add_expr('x /\ (y < 2)')
    assert gr1.is_realizable(z, aut)
    # \A \A unrealizable
    aut.init['env'] = aut.add_expr('(y < 1)')
    assert not gr1.is_realizable(z, aut)
    # \E \E realizable
    aut.init['env'] = aut.true
    aut.init['sys'] = aut.add_expr('x /\ (y < 3)')
    aut.qinit = '\E \E'
    z = aut.add_expr('x /\ (y < 2)')
    assert gr1.is_realizable(z, aut)
    # \E \E unrealizable
    aut.init['env'] = aut.true
    aut.init['sys'] = aut.add_expr('(y > 10)')
    aut.qinit = '\E \E'
    z = aut.true
    assert not gr1.is_realizable(z, aut)
    # \A \E realizable
    aut.moore = False
    aut.init['env'] = aut.true
    s = (
        '(x => (y = 1)) /\ '
        '((~ x) => (y = 4))')
    aut.init['sys'] = aut.add_expr(s)
    aut.qinit = '\A \E'
    z = aut.add_expr('y > 0')
    assert gr1.is_realizable(z, aut)
    # \A \E unrealizable
    s = (
        '(x => (y = 1)) /\ '
        '((~ x) => (y = 10))')
    aut.init['sys'] = aut.add_expr(s)
    aut.qinit = '\A \E'
    z = aut.true
    assert not gr1.is_realizable(z, aut)
    # \E \A realizable
    aut.moore = True
    s = 'x => (y = 1)'
    aut.init['sys'] = aut.add_expr(s)
    aut.qinit = '\E \A'
    z = aut.add_expr('y <= 2')
    assert gr1.is_realizable(z, aut)
    # \E \A unrealizable
    aut.init['env'] = aut.true
    aut.init['sys'] = aut.add_expr(r'''
        /\ (x => (y = 1))
        /\ ((~ x) => (y = 3))
        ''')
    aut.moore = True
    aut.qinit = '\E \A'
    z = aut.add_expr('y = 1 \/ y = 2')
    assert not gr1.is_realizable(z, aut)


def test_make_init():
    aut = trl.default_streett_automaton()
    aut.declare_variables(x='bool')
    aut.varlist.update(env=['x'], sys=['y'])
    internal_init = aut.true
    win = aut.true
    aut.qinit = '???'
    with assert_raises(ValueError):
        gr1._make_init(internal_init, win, aut)


def test_streett_qinit_exist_forall():
    aut = trl.default_streett_automaton()
    aut.declare_variables(x='bool', y=(0, 5))
    aut.varlist = dict(env=['x'], sys=['y'])
    aut.moore = True
    aut.qinit = '\E \A'
    aut.init['env'] = aut.add_expr('x')
    aut.init['sys'] = aut.add_expr('(x => (y = 4)) /\ y \in 0..5')
    aut.action['sys'] = aut.add_expr('y \in 0..5')
    # solve
    z, yij, xijk = gr1.solve_streett_game(aut)
    assert z == aut.add_expr('y \in 0..5'), aut.bdd.to_expr(z)
    # transducer
    gr1.make_streett_transducer(z, yij, xijk, aut)
    u = aut.init['impl']
    u_ = aut.add_expr('(y = 4) /\ (_goal = 0)')
    assert u == u_, aut.bdd.to_expr(u)


def test_trivial_winning_set():
    aut = trl.default_streett_automaton()
    aut.declare_variables(x='bool')
    aut.varlist = dict(env=list(), sys=['x'])
    aut.win['<>[]'] = [aut.add_expr(' ~ x')]
    triv, aut = gr1.trivial_winning_set(aut)
    assert triv == aut.true, aut.bdd.to_expr(triv)


def test_warn_moore_mealy():
    aut = trl.default_streett_automaton()
    aut.declare_variables(x='bool', y=(0, 25))
    aut.varlist = dict(env=['x'], sys=['y'])
    # Moore OK
    aut.moore = True
    aut.action['env'] = aut.add_expr("x /\ x' ")
    aut.action['sys'] = aut.add_expr("(y > 4) /\ (y' = 5)")
    aut.build()
    r = gr1._warn_moore_mealy(aut)
    assert r is True, r
    # Moore with env' in sys action
    aut.action['env'] = aut.add_expr("x /\ x' ")
    aut.action['sys'] = aut.add_expr("x' /\ (y > 4) /\ (y' = 5)")
    r = gr1._warn_moore_mealy(aut)
    assert r is False, r
    # Mealy with env' in sys action
    aut.moore = False
    r = gr1._warn_moore_mealy(aut)
    assert r is True, r
    # Mealy with sys' in env action
    aut.action['env'] = aut.add_expr("x /\ x' /\ (y' > 4)")
    aut.moore = False
    r = gr1._warn_moore_mealy(aut)
    assert r is False, r
    # Moore with sys' in env action
    aut.action['sys'] = aut.add_expr("(y > 4) /\ (y' = 5)")
    aut.moore = True
    r = gr1._warn_moore_mealy(aut)
    assert r is False, r


def action_refined(aut):
    """Return `True` if action of `'impl'` refines `'sys'`.

    @type aut_a, aut_b: `temporal.Automaton`
    """
    a = aut.action['sys']
    b = aut.action['impl']
    refined = aut.apply('=>', b, a)
    return refined == aut.true, aut.bdd.to_expr(b & ~ a)


def print_fol_bdd(u, bdd, table):
    """Print a first-order formula for node `u`.

    Example:

    ```
    aut = temporal.Automaton()
    aut.vars = dict(x=dict(type='int', dom=(0, 5), owner='sys'))
    aut.action['sys'] = ['x = 1']
    u = aut.action['sys'][0]
    print_fol_bdd(u, aut.bdd, aut.vars)
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
