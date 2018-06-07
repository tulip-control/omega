"""Algorithms for generalized Streett and Rabin games.

References
==========

Roderick Bloem, Barbara Jobstmann, Nir Piterman,
Amir Pnueli, Yaniv Sa'ar
    "Synthesis of reactive(1) designs"
    Journal of Computer and System Sciences
    Vol.78, No.3, pp.911--938, 2012


Robert Konighofer
    "Debugging formal specifications with
    simplified counterstrategies"
    Master's thesis
    Inst. for Applied Information Processing and Communications,
    Graz University of Technology, 2009
"""
# Copyright 2016 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
import logging
import copy

from omega.symbolic.prime import is_state_predicate
from omega.symbolic import fixpoint as fx
from omega.symbolic import fol as _fol
from omega.symbolic import prime as prm
from omega.symbolic import symbolic
from omega.symbolic import temporal as trl


logger = logging.getLogger(__name__)


def solve_streett_game(aut, rank=1):
    r"""Return winning set and iterants for Streett(1) game.

    The returned value takes into account actions and
    liveness, not initial conditions (i.e., it is the
    fixpoint before reasoning about initial conditions).

    Expects "env" and "sys" players. Writes:

      - `aut.varlist["env'"]`
      - `aut.varlist["sys'"]`

    @param aut: compiled game with <>[] \/ []<> winning
    @type aut: `temporal.Automaton`
    """
    assert rank == 1, 'only rank 1 supported for now'
    assert aut.bdd.vars or not aut.vars, (
        'first call `Automaton.build`')
    assert len(aut.win['<>[]']) > 0
    assert len(aut.win['[]<>']) > 0
    env_action = aut.action['env']
    sys_action = aut.action['sys']
    aut.build()
    z = aut.true
    zold = None
    while z != zold:
        zold = z
        cox_z = fx.step(env_action, sys_action, z, aut)
        xijk = list()
        yij = list()
        for goal in aut.win['[]<>']:
            goal &= cox_z
            y, yj, xjk = _attractor_under_assumptions(goal, aut)
            z &= y
            xijk.append(xjk)
            yij.append(yj)
    assert is_state_predicate(z), z.support
    return z, yij, xijk


def _attractor_under_assumptions(goal, aut):
    """Targeting `goal`, under unconditional assumptions."""
    env_action = aut.action['env']
    sys_action = aut.action['sys']
    xjk = list()
    yj = list()
    y = aut.false
    yold = None
    while y != yold:
        yold = y
        cox_y = fx.step(env_action, sys_action, y, aut)
        unless = cox_y | goal
        xk = list()
        for safe in aut.win['<>[]']:
            x = fx.trap(env_action, sys_action,
                        safe, aut, unless=unless)
            xk.append(x)
            y |= x
        yj.append(y)
        xjk.append(xk)
    return y, yj, xjk


def make_streett_transducer(z, yij, xijk, aut):
    """Return I/O `temporal.Automaton` implementing strategy.

    An auxiliary variable `_goal` is declared,
    to represent the counter of recurrence goals.
    The variable `_goal` is appended to `varlist['impl']`.
    """
    winning = z
    assert is_realizable(winning, aut)
    _warn_moore_mealy(aut)
    # declare goal counter var
    n_goals = len(aut.win['[]<>'])
    c = '_goal'
    c_max = n_goals - 1
    vrs = {c: (0, c_max)}
    aut.declare_variables(**vrs)
    aut.varlist['sys']
    # compile transducer with refined shared BDD
    env_init = aut.init['env']
    sys_init = aut.init['sys']
    env_action = aut.action['env']
    sys_action = aut.action['sys']
    holds = aut.win['<>[]']
    goals = aut.win['[]<>']
    # compute strategy from iterates
    # \rho_1: switch goals
    rho_1 = aut.false
    for i, goal in enumerate(goals):
        ip = (i + 1) % len(goals)
        s = "({c} = {i}) /\ ({c}' = {ip})".format(c=c, i=i, ip=ip)
        u = aut.add_expr(s)
        u &= goal
        rho_1 |= u
    zstar = _controllable_action(z, aut)
    rho_1 &= zstar
    # \rho_2: descent in basin
    rho_2 = aut.false
    for i, yj in enumerate(yij):
        s = "({c} = {i}) /\ ({c}' = {i})".format(c=c, i=i)
        count = aut.add_expr(s)
        rho_2j = aut.false
        basin = yj[0]
        for y in yj[1:]:
            # steps leading to next basin
            ystar = _controllable_action(basin, aut)
            rim = y & ~ basin
            u = rim & ystar
            rho_2j |= u
            basin |= y
        u = rho_2j & count
        rho_2 |= u
    # \rho_3: persistence holds
    rho_3 = aut.false
    for i, xjk in enumerate(xijk):
        s = "({c} = {i}) /\ ({c}' = {i})".format(c=c, i=i)
        count = aut.add_expr(s)
        rho_3j = aut.false
        used = aut.false
        for xk in xjk:
            assert len(xk) == len(holds), xk
            for x, hold in zip(xk, holds):
                # steps leading to next wait
                xstar = _controllable_action(x, aut)
                stay = x & ~ used
                used |= x
                u = stay & xstar
                u &= hold
                rho_3j |= u
        u = rho_3j & count
        rho_3 |= u
    # \rho
    u = rho_1 | rho_2
    u |= rho_3
    # counter `c` limits
    s = '{c} \in 0..{n}'.format(c=c, n=c_max)
    u &= aut.add_expr(s)
    # `sys_action` is already in the `\rho`
    # next is "useful" only if `env_action` depends on `y'`
    if not aut.plus_one:
        u |= ~ env_action
        if aut.moore:
            u = aut.forall(aut.varlist["env'"], u)
    assert u != aut.false
    symbolic._assert_support_moore(u, aut)
    aut.action['impl'] = u
    aut.varlist['impl'] = list(aut.varlist['sys']) + [c]
    aut.prime_varlists()
    # initial condition for counter
    # (no closure taken for counter)
    s = '{c} = 0'.format(c=c)
    count = aut.add_expr(s)
    _make_init(count, winning, aut)
    return aut.action['impl']


def solve_rabin_game(aut, rank=1):
    """Return winning set and iterants for Rabin(1) game.

    @param aut: compiled game with <>[] & []<> winning
    @type aut: `temporal.Automaton`
    """
    assert rank == 1, 'only rank 1 supported for now'
    assert aut.bdd.vars or not aut.vars, (
        'first call `Automaton.build`')
    # TODO: can these assertions be removed elegantly ?
    assert len(aut.win['<>[]']) > 0
    assert len(aut.win['[]<>']) > 0
    aut.build()
    z = aut.false
    zold = None
    zk = list()
    yki = list()
    xkijr = list()
    while z != zold:
        zold = z
        xijr = list()
        yi = list()
        for hold in aut.win['<>[]']:
            y, xjr = _cycle_inside(zold, hold, aut)
            z |= y
            xijr.append(xjr)
            yi.append(y)
        zk.append(z)
        yki.append(yi)
        xkijr.append(xijr)
    assert is_state_predicate(z), z.support
    return zk, yki, xkijr


def _cycle_inside(z, hold, aut):
    """Cycling through goals, while staying in `hold`."""
    env_action = aut.action['env']
    sys_action = aut.action['sys']
    cox_z = fx.step(env_action, sys_action, z, aut)
    g = cox_z | hold
    y = aut.true
    yold = None
    while y != yold:
        yold = y
        cox_y = fx.step(env_action, sys_action, y, aut)
        inside = cox_y & g
        xjr = list()
        for goal in aut.win['[]<>']:
            x, xr = _attractor_inside(inside, goal, aut)
            xjr.append(xr)
            y &= x
    return y, xjr


def _attractor_inside(inside, goal, aut):
    env_action = aut.action['env']
    sys_action = aut.action['sys']
    xr = list()
    x = aut.false
    xold = None
    while x != xold:
        xold = x
        cox_x = fx.step(env_action, sys_action, x, aut)
        x = cox_x | goal
        x &= inside
        x |= xold
        xr.append(x)
    return x, xr


def make_rabin_transducer(zk, yki, xkijr, aut):
    """Return O/I transducer for Rabin(1) game."""
    winning = zk[-1]
    assert is_realizable(winning, aut)
    _warn_moore_mealy(aut)
    dvars = dict(aut.vars)
    n_holds = len(aut.win['<>[]'])
    n_goals = len(aut.win['[]<>'])
    # add transducer memory as two indices:
    # - `w`: persistence hold index
    # - `c`: recurrence goal index
    w = '_hold'
    c = '_goal'
    n_w = n_holds - 1 + 1  # last value used as "none"
    n_c = n_goals - 1
    vrs = {w: (0, n_w), c: (0, n_c)}
    aut.declare_variables(**vrs)
    aut.varlist['sys']
    # compile
    env_init = aut.init['env']
    sys_init = aut.init['sys']
    env_action = aut.action['env']
    sys_action = aut.action['sys']
    goals = aut.win['[]<>']
    # compute strategy from iterates
    # \rho_1: descent in persistence basin
    s = "({c}' = {c}) /\ ({w}' = {none})".format(
        c=c, w=w, none=n_holds)
    count = aut.add_expr(s)
    rho_1 = aut.false
    basin = zk[0]
    for z in zk[1:]:
        zstar = _controllable_action(basin, aut)
        rim = z & ~ basin
        u = rim & zstar
        u &= count
        rho_1 |= u
        basin = z
    rho_2 = aut.false
    rho_3 = aut.false
    rho_4 = aut.false
    basin = aut.false
    for z, yi, xijr in zip(zk, yki, xkijr):
        cox_basin = fx.step(env_action, sys_action,
                            basin, aut)
        rim = z & ~ basin
        rim &= ~ cox_basin
        # rho_2: pick persistence set
        s = "({c}' = {c}) /\ ({w} = {none})".format(
            c=c, w=w, none=n_holds)
        count = aut.add_expr(s)
        u = rim & count
        v = aut.false
        for i, y in enumerate(yi):
            s = "{w}' = {i}".format(w=w, i=i)
            count = aut.add_expr(s)
            ystar = _controllable_action(y, aut)
            q = count & ystar
            v |= q
        u &= v
        rho_2 |= u
        # rho_3: descent in recurrence basin
        s = (
            "({c}' = {c}) /\ "
            "({w} /= {none}) /\ "
            "({w}' = {w})").format(
                c=c, w=w, none=n_holds)
        count = aut.add_expr(s)
        u = rim & count
        v = aut.false
        for i, xjr in enumerate(xijr):
            for j, (xr, goal) in enumerate(zip(xjr, goals)):
                s = (
                    "({c} = {j}) /\ "
                    " ({w} = {i})").format(c=c, w=w, i=i, j=j)
                count = aut.add_expr(s)
                x_basin = xr[0]
                p = aut.false
                for x in xr[1:]:
                    xstar = _controllable_action(x_basin, aut)
                    q = xstar & ~ x_basin
                    q &= x
                    p |= q
                    x_basin = x
                p &= count
                p &= ~ goal
                v |= p
        u &= v
        rho_3 |= u
        # rho_4: advance to next recurrence goal
        u = aut.false
        for j, goal in enumerate(goals):
            jp = (j + 1) % len(goals)
            s = "({c} = {j}) /\ ({c}' = {jp})".format(
                c=c, j=j, jp=jp)
            count = aut.add_expr(s)
            p = count & goal
            u |= p
        s = (
            "({w} /= {none}) /\ "
            "({w}' = {w})").format(
                c=c, w=w, none=n_holds)
        count = aut.add_expr(s)
        u &= count
        u &= rim
        v = aut.false
        for i, y in enumerate(yi):
            s = "{w} = {i}".format(w=w, i=i)
            count = aut.add_expr(s)
            ystar = _controllable_action(y, aut)
            q = count & ystar
            v |= q
        u &= v
        rho_4 |= u
        # update
        basin = z
    # \rho
    u = rho_1 | rho_2
    u |= rho_3
    u |= rho_4
    # counter limits
    s = '({w} \in 0..{n_w}) /\ ({c} \in 0..{n_c})'.format(
        w=w, n_w=n_w, c=c, n_c=n_c)
    u &= aut.add_expr(s)
    if not aut.plus_one:
        u |= ~ env_action
        if aut.moore:
            u = aut.forall(aut.varlist["env'"], u)
    assert u != aut.false
    symbolic._assert_support_moore(u, aut)
    aut.action['impl'] = u
    aut.varlist['impl'] = list(aut.varlist['sys']) + [w, c]
    aut.prime_varlists()
    # initial condition for counter
    s = '({c} = 0) /\ ({w} = {none})'.format(
        c=c, w=w, none=n_holds)
    count = aut.add_expr(s)
    _make_init(count, winning, aut)
    return aut.action['impl']


def is_realizable(win, aut):
    """Return `True` if, and only if, `aut` wins from `z`.

    @param win: bdd node
    @param aut: `temporal.Automaton`
    """
    sys_init = aut.init['sys']
    env_init = aut.init['env']
    sys_vars = aut.varlist['sys']
    env_vars = aut.varlist['env']
    # decouple stepwise form from sharing of state initially
    if aut.plus_one:
        init = sys_init & (win | ~ env_init)
        form = 'SysInit /\ (EnvInit => Win)'
    else:
        init = (sys_init & win) | ~ env_init
        form = 'EnvInit => (SysInit /\ Win)'
    qinit = aut.qinit
    if qinit == '\A \A':
        assert sys_init == aut.true
        u = win | ~ env_init
        r = (u == aut.true)
        msg = (
            'The initial condition requirement:\n'
            '\A x, y:  EnvInit => Win\n'
            'does not hold, so some `EnvInit` states are losing.')
    elif qinit == '\E \E':
        assert env_init == aut.true
        vrs = env_vars + sys_vars
        u = aut.exist(vrs, win & sys_init)
        r = (u == aut.true)
        msg = (
            'The initial condition requirement:\n'
            '\E x, y:  SysInit /\ Win\n'
            'does not hold, so no `SysInit` states are winning.')
    elif qinit == '\A \E':
        u = aut.exist(sys_vars, init)
        u = aut.forall(env_vars, u)
        r = (u == aut.true)
        msg = (
            'The initial condition requirement:\n'
            '\A x:  \E y:  {form}\n'
            'does not hold, so for some `EnvInit` states, '
            'the component cannot pick an initial `SysInit` state \n'
            'that is also winning.'
            ).format(form=form)
    elif qinit == '\E \A':
        u = aut.forall(env_vars, init)
        u = aut.exist(sys_vars, u)
        r = (u == aut.true)
        msg = (
            'The initial condition requirement:\n'
            '\E y:  \A x:  {form}\n'
            'does not hold, so the component cannot pick '
            'a single `SysInit` state such that for any \n'
            '`EnvInit` state, the initial state be winning.'
            ).format(form=form)
    else:
        raise ValueError(
            'unknown `qinit` value "{q}"'.format(
                q=qinit))
    if not r:
        print(msg)
    return r


def _controllable_action(target, aut):
    """Return controllable transitions for progress.

    Compared to CPre, this has "half" the quantification.
    """
    env_action = aut.action['env']
    sys_action = aut.action['sys']
    u = prm.prime(target, aut)
    if aut.plus_one:
        # sys_action /\ (env_action => target')
        u |= ~ env_action
        u &= sys_action
    else:
        # env_action => (sys_action /\ target')
        u &= sys_action
        u |= ~ env_action
    if aut.moore:
        # \A uvars'
        u = aut.forall(aut.varlist["env'"], u)
    return u


def _make_init(internal_init, win, aut):
    """Return initial conditions for implementation.

    Depending on `aut.qinit`,
    synthesize the initial condition `aut.init['impl']`
    using the winning states `win`.

    The cases are:

    - `\A \A`:  `InternalInit`
    - `\E \E`:  `InternalInit /\ Win /\ SysInit`
    - `\A \E`:

      - `plus_one is True`:
        ```
        /\ SysInit /\ (EnvInit => Win)
        /\ InternalInit
        ```

      - `plus_one is False`:
        ```
        /\ EnvInit => (SysInit /\ Win)
        /\ InternalInit
        ```

    - `\E \A`:

      - `plus_one is True`:
        ```
        /\ \A EnvVars:  SysInit /\ (EnvInit => Win)
        /\ InternalInit
        ```

      - `plus_one is False`:
        ```
        /\ \A EnvVars:  EnvInit => (SysInit /\ Win)
        /\ InternalInit
        ```

    where `InternalInit` is the initial condition for internal variables.

    @param internal_init: initial condition for
        internal variables.
    """
    sys_init = aut.init['sys']
    env_init = aut.init['env']
    env_vars = aut.varlist['env']
    qinit = aut.qinit
    plus_one = aut.plus_one
    # In `omega.games.enumeration` both of these reduce
    # to `sys_init & win` over those states that are
    # enumerated as initial, because only states that
    # satisfy `env_init` are enumerated--assuming
    # `env_init` is independent of sys vars.
    if plus_one:
        form = sys_init & (win | ~ env_init)
    else:
        form = (sys_init & win) | ~ env_init
    assert is_state_predicate(form)
    if qinit == '\A \A':
        # shared-state, env picks initial state
        init = aut.true
    elif qinit == '\E \E':
        # shared-state, sys picks initial state
        init = win & sys_init
    elif qinit == '\A \E':
        # disjoint-state
        init = form
    elif qinit == '\E \A':
        # disjoint-state
        init = aut.forall(env_vars, form)
    else:
        raise ValueError(
            'unknown `qinit` value "{q}"'.format(q=qinit))
    assert init != aut.false
    assert is_state_predicate(init)
    aut.init['impl'] = init & internal_init


def _warn_moore_mealy(aut):
    """Warn the user if they define actions suspect of error."""
    env_action = aut.action['env']
    sys_action = aut.action['sys']
    moore = aut.moore
    env_support = aut.support(env_action)
    sys_support = aut.support(sys_action)
    env_depends_on_primed_sys = env_support.intersection(
        aut.varlist["sys'"])
    sys_depends_on_primed_env = sys_support.intersection(
        aut.varlist["env'"])
    r = True
    if moore and sys_depends_on_primed_env:
        r = False
        print(
            'WARNING: Moore sys, but sys depends on '
            'primed env vars:\n {r}'.format(
                r=sys_depends_on_primed_env))
    if not moore and env_depends_on_primed_sys:
        r = False
        print((
            'WARNING: Mealy sys, and assumption depends on '
            'primed sys vars.\n'
            'If env has to be Mealy too, '
            'then you can get cyclic dependencies.\n'
            'Primed sys vars:\n {r}').format(
                r=env_depends_on_primed_sys))
    if env_depends_on_primed_sys:
        r = False
        print((
            'ATTENTION: assumption depends on primed sys vars:\n'
            '{r}\n'
            'Is a Mealy env realistic for your problem ?').format(
                r=env_depends_on_primed_sys))
    return r


def trivial_winning_set(aut_streett):
    """Return set of trivially winning nodes for Streett(1).

    @return: `(trivial, aut_streett)` where:
        - `trivial`: node in `aut_streett.bdd`
        - `aut_streett`: `temporal.Automaton`
    """
    aut_rabin = trl.default_rabin_automaton()
    aut_rabin.bdd = aut_streett.bdd
    aut_rabin.vars = copy.deepcopy(aut_streett.vars)
    # swap vars and actions
    aut_rabin.varlist['env'] = list(aut_streett.varlist['sys'])
    aut_rabin.varlist['sys'] = list(aut_streett.varlist['env'])
    aut_rabin.action['env'] = aut_streett.action['sys']
    aut_rabin.action['sys'] = aut_streett.action['env']
    aut_rabin.init['env'] = aut_streett.init['sys']
    aut_rabin.init['sys'] = aut_streett.init['env']
    win = [~ w for w in aut_streett.win['<>[]']]
    aut_rabin.win['[]<>'] = win
    # needed because we changed bdd
    aut_rabin.win['<>[]'] = [aut_rabin.true]
    # solve
    win_streett, _, _ = solve_streett_game(aut_streett)
    zk, _, _ = solve_rabin_game(aut_rabin)
    win_rabin = zk[-1]
    # find trivial win set
    # win_rabin_ = _copy_bdd(win_rabin,
    #                        aut_rabin.bdd, aut_streett.bdd)
    trivial = win_streett & ~ win_rabin
    return trivial, aut_streett


def _map_nested_lists(f, x, *arg, **kw):
    """Recursively map lists, with non-lists at the bottom.

    Useful for applying `dd.bdd.copy_bdd` to several lists.
    """
    if isinstance(x, list):
        return [_map_nested_lists(f, y, *arg, **kw) for y in x]
    else:
        return f(x, *arg, **kw)


def _copy_bdd(u, a, b):
    """Copy bdd `u` from manager `a` to `b`.

    No effect if `a is b`.
    """
    if a is b:
        return u
    return a.copy(u, b)
