"""Conversion of semi-symbolic to symbolic automata.

Re-implementation of `tulip.synth`.
"""
# Copyright 2015-2017 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
from __future__ import absolute_import
import logging
import warnings

from omega.logic import syntax as stx
from omega.symbolic import temporal as trl


logger = logging.getLogger(__name__)


def graph_to_logic(
        g, nodevar, ignore_initial,
        receptive=False, self_loops=False,
        aut=None):
    """Flatten labeled graph to temporal logic formulas.

    @param g: `TransitionSystem`

    The attribute `g.owner` defines who selects the next node.
    The attribute `g.env_vars` determines who controls each variable.

    @param g: `TransitionSystem`
    @param nodevar: variable that stores current node
    @type nodevar: `str`
    @param ignore_initial: if `False`, then add initial condition
        using `g.initia_nodes`.
    @type ignore_initial: `bool`
    @param receptive: if `True`, then add assumptions to
        ensure receptiveness at each node.
    @param self_loops: if `True`, then add all self-loops
    @param aut: define in this automaton.
        If `None`, return fresh `temporal.Automaton`

    @return: temporal formulas representing `g`.
    @rtype: `temporal.Automaton`
    """
    (env_init, env_tran,
     sys_init, sys_tran) = _graph_to_formulas(
        g, nodevar, ignore_initial,
        receptive=receptive, self_loops=self_loops)
    # package as automaton
    dom = _nodevar_dom(g)
    if aut is None:
        aut = trl.Automaton()
    d = dict(g.vars)
    d[nodevar] = dom
    aut.declare_variables(**d)
    aut.varlist['env'] = list(g.env_vars)
    aut.varlist['sys'] = [k for k in g.vars if k not in g.env_vars]
    aut.varlist[g.owner].append(nodevar)
    aut.init.update(
        env=_add_expr(env_init, aut),
        sys=_add_expr(sys_init, aut))
    aut.action.update(
        env=_add_expr(env_tran, aut),
        sys=_add_expr(sys_tran, aut))
    return aut


def _graph_to_formulas(
        g, nodevar, ignore_initial,
        receptive=False, self_loops=False):
    """Return strings of init and actions."""
    assert g.assert_consistent()
    assert len(g) > 0
    dvars = dict(g.vars)
    dvars[nodevar] = _nodevar_dom(g)
    p, _ = _prime_dict(dvars)
    dvars.update(p)
    # convert to logic
    init = _init_from_ts(g.initial_nodes, nodevar,
                         dvars, ignore_initial)
    tmp_init, nodepred = _node_var_trans(g, nodevar, dvars)
    sys_tran, env_tran = list(), list()
    if g.owner == 'sys':
        sys_init = init + tmp_init
        r = _sys_trans(g, nodevar, dvars)
        if self_loops:
            r = "({r}) \/ ({var}' = {var})".format(
                r=r, var=nodevar)
        sys_tran.append(r)
        sys_tran.extend(nodepred)
        env_init = list()
        if receptive:
            r = _env_trans_from_sys_ts(g, nodevar, dvars)
            env_tran.append(r)
    elif g.owner == 'env':
        sys_init = list()
        env_init = init + tmp_init
        r = _env_trans(g, nodevar, dvars, self_loops)
        if self_loops:
            r = "({r}) \/ ({var}' = {var})".format(
                r=r, var=nodevar)
        env_tran.append(r)
        env_tran.extend(nodepred)
    else:
        raise Exception('owner is neither "sys" nor "env".')
    return env_init, env_tran, sys_init, sys_tran


def _add_expr(c, aut):
    """Return BDD for conjunction of expressions in `c`."""
    return aut.add_expr(stx.conj(c))


def _nodevar_dom(g):
    """Return range of current node index."""
    assert all(isinstance(u, int) for u in g)
    return (min(g), max(g))


def _node_var_trans(g, nodevar, dvars):
    """Return data flow constraint on variables labeling nodes."""
    init = list()
    trans = list()
    # no AP labels ?
    if not dvars:
        return (init, trans)
    for u, d in g.nodes(data=True):
        pre = _assign(nodevar, u, dvars)
        r = _to_action(d, dvars)
        if r == 'True':
            continue
        # initial node vars
        init.append('~ ({pre}) \/ ({r})'.format(pre=pre, r=r))
        # transitions of node vars
        trans.append("((({pre}) => ({r}))')".format(pre=pre, r=r))
    return (init, trans)


def _init_from_ts(
        initial_nodes, nodevar,
        dvars, ignore_initial=False):
    """Return initial condition."""
    if ignore_initial:
        return list()
    if not initial_nodes:
        raise Exception('Transition system without initial states.')
    return [stx.disj(_assign(nodevar, u, dvars) for u in initial_nodes)]


def _sys_trans(g, nodevar, dvars):
    """Convert transition relation to safety formula."""
    logger.debug('modeling sys transitions in logic')
    sys_trans = list()
    for u in g:
        pre = _assign(nodevar, u, dvars)
        # no successors ?
        if not g.succ.get(u):
            logger.debug('node: {u} is deadend !'.format(u=u))
            sys_trans.append('({pre}) => False'.format(pre=pre))
            continue
        post = list()
        for u, v, d in g.edges(u, data=True):
            t = dict(d)
            t[stx.prime(nodevar)] = v
            r = _to_action(t, dvars)
            post.append(r)
        c = '({pre}) => ({post})'.format(pre=pre, post=stx.disj(post))
        sys_trans.append(c)
    s = stx.conj(sys_trans, sep='\n')
    return s


def _env_trans_from_sys_ts(g, nodevar, dvars):
    """Return safety assumption to prevent env from blocking sys."""
    denv = {k: v for k, v in dvars.items() if k in g.env_vars}
    env_trans = list()
    for u in g:
        # no successor states ?
        if not g.succ.get(u):
            continue
        # collect possible next env actions
        c = set()
        for u, w, d in g.edges(u, data=True):
            t = _to_action(d, denv)
            if not t:
                continue
            c.add(t)
        # no next env actions ?
        if not c:
            continue
        post = stx.disj(c)
        pre = _assign(nodevar, u, dvars)
        env_trans.append('(({pre}) => ({post}))'.format(
            pre=pre, post=post))
    s = stx.conj(env_trans, sep='\n')
    return s


def _env_trans(g, nodevar, dvars, self_loops):
    """Convert environment transitions to safety formula.

    @type g: `networkx.MultiDigraph`
    @param nodevar: name of variable representing current node
    @type nodevar: `str`
    @type dvars: `dict`
    """
    env_trans = list()
    for u in g:
        pre = _assign(nodevar, u, dvars)
        # no successors ?
        if not g.succ.get(u):
            env_trans.append('{pre} => False'.format(pre=pre))
            if not self_loops:
                warnings.warn(
                    'Environment dead-end found.\n'
                    'If sys can force env to dead-end,\n'
                    'then GR(1) assumption becomes False,\n'
                    'and spec trivially True.')
            continue
        post = list()
        sys = list()
        for u, v, d in g.out_edges(u, data=True):
            # action
            t = dict(d)
            t[stx.prime(nodevar)] = v
            r = _to_action(t, dvars)
            post.append(r)
            # what sys vars ?
            t = {k: v for k, v in d.items()
                 if k not in g.env_vars}
            r = _to_action(t, dvars)
            sys.append(r)
        # avoid sys winning env by blocking all edges
        # post.append(stx.conj_neg(sys))
        env_trans.append('({pre}) => ({post})'.format(
            pre=pre, post=stx.disj(post)))
    s = stx.conj(env_trans, sep='\n')
    return s


def _to_action(d, dvars):
    """Return `str` conjoining assignments and `"formula"` in `d`.

    @param d: (partial) mapping from variables in `dvars`
        to values in their range, defined by `dvars`
    @type d: `dict`
    @type dvars: `dict`
    """
    c = list()
    if 'formula' in d:
        c.append(d['formula'])
    for k, v in d.items():
        if k not in dvars:
            continue
        s = _assign(k, v, dvars)
        c.append(s)
    return stx.conj(c)


def _assign(k, v, dvars):
    """Return `str` of equality of variable `k` to value `v`.

    @type k: `str`
    @type v: `str` or `int`
    @type dvars: `dict`
    """
    typ = dvars[k]
    if typ == 'bool':
        s = '{k} <=> {v}'.format(k=k, v=v)
    elif isinstance(typ, tuple) and len(typ) == 2:  # integer
        s = '{k} = {v}'.format(k=k, v=v)
    elif isinstance(typ, list):  # string enumeration
        s = '{k} = "{v}"'.format(k=k, v=v)
    else:
        raise Exception('variable type hint is: {dtype}'.format(
            dtype=dtype))
    return _pstr(s)


def _prime_dict(d):
    """Return `dict` with primed keys and `dict` mapping to them."""
    p = dict((stx.prime(k), d[k]) for k in d)
    d2p = {k: stx.prime(k) for k in d}
    return p, d2p


def _pstr(x):
    return '({x})'.format(x=x)
