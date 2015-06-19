import logging
import pprint
from dd import bdd as _bdd
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
    assert z == a.bdd.True, z
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
    assert len(t.init['sys']) == 1, t.init
    (init,) = t.init['sys']
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
    assert zk[-1] == a.bdd.True, zk
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
    assert len(t.init['sys']) == 1, t.init
    (init,) = t.init['sys']
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
    assert win_set == aut.bdd.False, win_set


def test_rabin_deadend():
    a = symbolic.Automaton()
    a.acceptance = 'Rabin(1)'
    a.vars = dict(x=dict(type='int', dom=(0, 101), owner='sys'))
    a.action['sys'] = ["(x = 1) & (x' = 96 - x)"]
    symbolic.fill_blanks(a)
    aut = a.build()
    zk, _, _ = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.False, win_set


def test_streett_always_x():
    # always x
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='sys'))
    a.action['sys'] = ["x'"]
    symbolic.fill_blanks(a)
    # solve
    aut = a.build()
    z, yij, xijk = gr1.solve_streett_game(aut)
    assert z == aut.bdd.True, z
    # transducer
    t = gr1.make_streett_transducer(z, yij, xijk, aut)
    # init
    (init,) = t.init['sys']
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
    a.action['sys'] = ['!x']
    aut = a.build()
    # solve
    z, yij, xijk = gr1.solve_streett_game(aut)
    assert z == aut.add_expr('!x'), aut.bdd.to_expr(z)
    # tranducer
    t = gr1.make_streett_transducer(z, yij, xijk, aut)
    assert action_refined(aut, t)
    (init,) = t.init['sys']
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
    assert win_set == aut.bdd.True, win_set
    # transducer
    t = gr1.make_rabin_transducer(zk, yki, xkijr, aut)
    # init
    (init,) = t.init['sys']
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
    (init,) = t.init['sys']
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
    a.action['sys'] = ["x -> !x'"]
    a.win['[]<>'] = ['x']
    symbolic.fill_blanks(a)
    # solve
    aut = a.build()
    z, yij, xijk = gr1.solve_streett_game(aut)
    assert z == aut.bdd.True, z
    # transducer
    t = gr1.make_streett_transducer(z, yij, xijk, aut)
    (init,) = t.init['sys']
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
    a.vars = dict(x=dict(type='bool', owner='sys'))
    a.action['sys'] = ["x -> !x'"]
    a.win['[]<>'] = ['x']
    symbolic.fill_blanks(a, rabin=True)
    # solve
    aut = a.build()
    zk, yki, xkijr = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.True, aut.bdd.to_expr(win_set)
    # transducer
    t = gr1.make_rabin_transducer(zk, yki, xkijr, aut)
    assert action_refined(aut, t)
    (init,) = t.init['sys']
    s = '(_goal = 0) & (_hold = 1)'
    init_ = t.add_expr(s)
    assert init == init_, t.bdd.to_expr(init)
    (action,) = t.action['sys']
    # regression
    s = (
        "(_goal = 0) & (_goal' = 0) & "
        "(_hold' = 0) & "
        "ite(_hold = 0, x <-> !x', x -> !x')")
    action_ = t.add_expr(s)
    assert action == action_, t.bdd.to_expr(action)


def test_rabin_persistence():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='sys'))
    a.init['sys'] = ['!x']
    a.win['<>[]'] = ['x']
    symbolic.fill_blanks(a, rabin=True)
    # solve
    aut = a.build()
    zk, yki, xkijr = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.True, aut.bdd.to_expr(win_set)
    # tranducer
    t = gr1.make_rabin_transducer(zk, yki, xkijr, aut)
    assert action_refined(aut, t)
    (init,) = t.init['sys']
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
    assert win_set == aut.bdd.False, aut.bdd.to_expr(win_set)


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
    assert win_set == aut.bdd.True, aut.bdd.to_expr(win_set)
    # transducer
    t = gr1.make_rabin_transducer(zk, yki, xkijr, aut)
    assert action_refined(aut, t)
    (init,) = t.init['sys']
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
    a.action['env'] = ['x']
    a.action['sys'] = ['x']
    symbolic.fill_blanks(a)
    # solve
    aut = a.build()
    z, yij, xijk = gr1.solve_streett_game(aut)
    assert z == aut.bdd.True, z
    # transducer
    t = gr1.make_streett_transducer(z, yij, xijk, aut)
    assert action_refined(aut, t)
    (init,) = t.init['sys']
    assert init == t.add_expr('_goal = 0'), t.bdd.to_expr(init)
    (action,) = t.action['sys']
    action_ = t.add_expr("(_goal = 0) & (_goal' = 0) & x")
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
    (init,) = t.init['sys']
    s = '(_goal = 0) & (_hold = 1)'
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
    assert win_set == t.bdd.False, t.bdd.to_expr(win_set)
    with assert_raises(AssertionError):
        gr1.make_rabin_transducer(zk, yki, xkijr, aut)


def test_streett_with_liveness_assumption():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='env'),
                  y=dict(type='int', dom=(0, 2), owner='sys'))
    a.action['sys'] = [
        "((y = 0) & !x) -> (y' = 0)",
        "(y = 0) -> (y' < 2)",
        "(y = 1) -> (y' = 0)",
        "(y = 2) -> False"]
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
    (init,) = t.init['sys']
    assert init == t.add_expr('(y < 2) & (_goal = 0)'), t.bdd.to_expr(init)
    (action,) = t.action['sys']
    s = (
        "( (y = 0) -> ite(x, (y' = 1), (y' = 0)) ) & "
        "( (y = 1) -> (y' = 0) ) & "
        "( (_goal = 0) & (_goal' = 0) ) & "
        "( (y != 2) & (y != 3) )")
    action_ = t.add_expr(s)
    sat = list(t.bdd.sat_iter(action))
    sys_action = aut.action['sys'][0]
    sys_action = _bdd.copy_bdd(sys_action, aut.bdd, t.bdd)
    u = t.bdd.apply('->', action, sys_action)
    assert u == t.bdd.True, u
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
    streett_win_set = _bdd.copy_bdd(z, aut.bdd, bdd)
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
    assert z == aut.bdd.True, aut.bdd.to_expr(z)
    # transducer
    t = gr1.make_streett_transducer(z, yij, xijk, aut)
    assert action_refined(aut, t)
    (action,) = t.action['sys']
    # print_fol_bdd(action, t.bdd, t.vars)
    # enumeration.dump_relation(action, t)
    s = (
        "((x & (_goal = 0)) -> (_goal' = 1)) & "
        "((!x & (_goal = 1)) -> (_goal' = 0)) & "
        "((!x & (_goal = 0)) -> (x' & (_goal' = 0))) & "
        "((x & (_goal = 1)) -> (!x' & (_goal' = 1)))")
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
    assert win_set == aut.bdd.False, aut.bdd.to_expr(win_set)


def test_rabin_2_goals():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='env'),
                  y=dict(type='bool', owner='sys'))
    a.win['[]<>'] = ['x -> y']
    symbolic.fill_blanks(a, rabin=True)
    aut = a.build()
    # solve
    zk, _, _ = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.True, aut.bdd.to_expr(win_set)
    #
    # unrealizable
    a.win['<>[]'] = ['! y']
    aut = a.build()
    zk, _, _ = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.False, aut.bdd.to_expr(win_set)
    #
    # realizable again
    a.win['<>[]'] = ['y']
    aut = a.build()
    zk, _, _ = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.True, aut.bdd.to_expr(win_set)
    #
    # unrealizable
    a.win['[]<>'] = ['x -> y', '!y']
    aut = a.build()
    zk, _, _ = gr1.solve_rabin_game(aut)
    win_set = zk[-1]
    assert win_set == aut.bdd.False, aut.bdd.to_expr(win_set)


def test_trivial_winning_set():
    a = symbolic.Automaton()
    a.vars = dict(x=dict(type='bool', owner='sys'))
    a.win['<>[]'] = ['!x']
    symbolic.fill_blanks(a)
    triv, aut = gr1.trivial_winning_set(a)
    assert triv == aut.bdd.True, aut.bdd.to_expr(triv)


def action_refined(aut_a, aut_b, owner='sys'):
    """Return `True` if action of `aut_b` refines `aut_a`.

    @type aut_a, aut_b: `symbolic.Automaton`
    """
    bdd_a = aut_a.bdd
    bdd_b = aut_b.bdd
    a = aut_a.action[owner][0]
    b = aut_b.action[owner][0]
    if bdd_a is not bdd_b:
        a_cp = _bdd.copy_bdd(a, bdd_a, bdd_b)
    else:
        a_cp = a
    refined = bdd_b.apply('->', b, a_cp)
    return refined == bdd_b.True


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
