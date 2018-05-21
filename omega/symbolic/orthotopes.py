"""Boxes with integer size."""
# Copyright 2016-2018 by California Institute of Technology
# All rights reserved. Licensed under 3-clause BSD.
#
import logging

import natsort

from omega.logic import syntax as stx
from omega.symbolic.prime import support_issubset
from omega.symbolic.prime import joint_support
from omega.symbolic import _type_hints as tyh


log = logging.getLogger(__name__)


def partial_order(px, fol):
    """Return `u <= p` and `p <= u`."""
    ux = {
        x: dict(
            a=stx._prime_like(d['a']),
            b=stx._prime_like(d['b']))
        for x, d in px.items()}
    varmap = parameter_varmap(ux, px)
    u_leq_p = subseteq(varmap, fol)
    varmap = parameter_varmap(px, ux)
    p_leq_u = subseteq(varmap, fol)
    return u_leq_p, p_leq_u


def essential_orthotopes(f, prm, fol):
    """Return essential prime orthotopes of `f`."""
    log.info('---- essential orthotopes ----')
    p_is_prime = prime_implicants(f, prm, fol)
    q_is_prime = fol.let(prm.p_to_q, p_is_prime)
    # add to quantify u, v, so that we can rename
    x_in_p = x_in_implicant(prm, fol)
    x_in_q = fol.let(prm.p_to_q, x_in_p)
    # del x_in_p
    x = ', '.join(prm._px)
    q = ', '.join(prm.q_vars)
    s = (
        '{p_is_prime} /\ '
        r'\E {x}:  ( '
        '    {f} /\ '
        r'    \A {q}:  ( '
        '        ( '
        '            {q_is_prime} /\ '
        '            ~ {p_eq_q} '
        '        ) '
        '        => ~ {x_in_q}'
        '    )'
        ')').format(
            p_is_prime=p_is_prime,
            q_is_prime=q_is_prime,
            p_eq_q=prm.p_eq_q,
            x_in_q=x_in_q,
            f=f, x=x, q=q)
    r = fol.add_expr(s)
    log.info('==== essential orthotopes ====')
    return r


def prime_implicants(f, prm, fol):
    """Return dominators of implicants."""
    log.info('----- prime orthotopes ----')
    assert support_issubset(f, prm.x_vars, fol)
    p_is_implicant = _implicant_orthotopes(f, prm, fol)
    q_is_implicant = fol.let(prm.p_to_q, p_is_implicant)
    r = q_is_implicant & prm.p_leq_q
    r = prm.p_eq_q | ~ r
    r = fol.forall(prm.q_vars, r)
    r &= p_is_implicant
    '''
    q = ', '.join(prm.q_vars)
    s = (
        '{p_is_implicant} /\ '
        r'\A {q}:  ( '
        '     ({q_is_implicant} /\ {p_leq_q})'
        '     => {p_eq_q}'
        ')').format(
            p_is_implicant=p_is_implicant,
            q_is_implicant=q_is_implicant,
            p_leq_q=prm.p_leq_q,
            p_eq_q=prm.p_eq_q,
            q=prm.q_vars)
    r = fol.add_expr(s)
    '''
    log.info('==== prime orthotopes ====')
    return r


def _implicant_orthotopes(f, prm, fol):
    """Return orthotopes that imply `f`.

    Caution: `fol` type hints are ignored.
    """
    log.info('---- implicant orthotopes ----')
    x_vars = prm.x_vars
    assert support_issubset(f, x_vars, fol)
    x = ', '.join(x_vars)
    h = x_in_implicant(prm, fol)
    nonempty = _orthotope_nonempty(prm._px, fol)
    s = (
        '{nonempty} /\ '
        '\A {x}:  {h} => {f} ').format(
            x=x, h=h, f=f, nonempty=nonempty)
    r = fol.add_expr(s)
    log.info('==== implicant orthotopes ====')
    return r


def embed_as_implicants(f, prm, fol):
    px = prm._px
    ax = {x: d['a'] for x, d in px.items()}
    u = fol.let(ax, f)
    v = _orthotope_singleton(px, fol)
    return u & v


def _embed_as_implicants_naive(f, px, fol):
    """Return product representation of minterms."""
    x_as_ab = {x: dict(a=x, b=x) for x in px}
    varmap = parameter_varmap(px, x_as_ab)
    r = eq(varmap, fol)
    return fol.exist(x_as_ab, r & f)


# slower than `_orthotope_singleton`
# needs `from omega.symbolic import fol as _fol`
def _orthotope_singleton_wo_parsing(px, fol):
    """Return BDD that orthotope contains single point."""
    a_b = {d['a']: d['b'] for d in px.values()}
    bitmap = _fol._refine_renaming(a_b, fol.vars)
    bdd = fol.bdd
    r = bdd.true
    for b1, b2 in bitmap.items():
        u = bdd.var(b1)
        v = bdd.var(b2)
        u = bdd.apply('<=>', u, v)
        r &= u
    r_ = _orthotope_signleton(px, fol)
    assert r == r_, (r, r_)
    return r


def _orthotope_singleton(px, fol):
    """Return BDD that orthotope contains single point."""
    s = stx.conj(
        '({a} = {b})'.format(
            a=d['a'], b=d['b'])
        for x, d in px.items())
    r = fol.add_expr(s)
    return r


def _orthotope_nonempty(abx, fol):
    """Return condition that orthotope be non-empty."""
    s = stx.conj(
        '({a} <= {b})'.format(
            a=d['a'], b=d['b'])
        for x, d in abx.items())
    r = fol.add_expr(s)
    return r


def x_in_implicant(prm, fol):
    r"""Return `x \in concretization(prm)`."""
    px = prm._px
    s = stx.conj('''
           ({a} <= {x})
        /\ ({x} <= {b})
        '''.format(
            x=x, a=d['a'], b=d['b'])
        for x, d in px.items())
    r = fol.add_expr(s)
    return r


def subseteq(varmap, fol):
    r"""Return `ab \subseteq uv`.

    This is the partial order defined by the subset relation.
    In the general formulation `\sqsubseteq`.
    """
    s = stx.conj('''
           ({u} <= {a})
        /\ ({b} <= {v})
        '''.format(a=a, b=b, u=u, v=v)
            for (a, b), (u, v) in varmap.items())
    r = fol.add_expr(s)
    return r


def eq(varmap, fol):
    """Return `ab = uv`.

    The parameterization defines an injective mapping from
    parameter assignments to orthotopes. This is why equality
    of orthotopes is equivalent to equality of parameter values.
    """
    s = stx.conj('''
           ({a} = {u})
        /\ ({b} = {v})
        '''.format(a=a, b=b, u=u, v=v)
        for (a, b), (u, v) in varmap.items())
    r = fol.add_expr(s)
    return r


def implicants_intersect(prm, fol):
    """Return `ab \cap uv # \emptyset`.

    Equivalent to

    \E x:  /\ x \in concretization(ab)
           /\ x \in concretization(uv)

    The representation of orthotopes as products of
    intervals allows for a direct construction that
    avoids quantification over `x`.
    """
    # disjoint intervals in at least one dimension
    s = stx.disj('''
           ({b} < {u})
        \/ ({v} < {a})
        '''.format(a=a, b=b, u=u, v=v)
            for (a, b), (u, v) in prm._varmap.items())
    r = fol.add_expr(s)
    return ~ r


def plot_orthotopes(u, abx, axvars, fol, ax):
    """Plot a polytope for each orthotope in `u`.

    @param axvars: `list` that defines which variable
        spans each dimension of the plot.
    """
    try:
        import polytope as poly
    except ImportError:
        raise ImportError(
            '`orthotopes` failed to import `polytope`.\n'
            'No plotting of orthotopes.')
    c = _orthotopes_iter(u, fol)
    eps = 0.1
    cycol = cycle('bgrcmk')
    for product in c:
        x, y = axvars
        a_x = abx[x]['a']
        b_x = abx[x]['b']
        a_y = abx[y]['a']
        b_y = abx[y]['b']
        xmin = product[a_x]
        xmax = product[b_x]
        ymin = product[a_y]
        ymax = product[b_y]
        # if a = b add a small amount
        if xmin == xmax:
            xmin -= eps
            xmax += eps
        if ymin == ymax:
            ymin -= eps
            ymax += eps
        size = [[xmin, xmax], [ymin, ymax]]
        p = poly.box2poly(size)
        color = next(cycol)
        p.plot(ax=ax, color=color, alpha=0.5)


def list_expr(
        cover, prm, fol,
        simple=False,
        use_dom=False, latex=False):
    """Return `list` of `str`, each an orthotope in `cover`.

    @param simple: if `True`, then return expression
        that can be parsed by `fol.add_expr`.
    @param use_dom: omit conjuncts that contain dom of var
        assumes that `|= care => type_hints`
    """
    px = prm._px
    xp = _map_parameters_to_vars(px)
    support = fol.support(cover)
    keys = {xp[k] for k in support}
    keys = natsort.natsorted(keys)
    c = _orthotopes_iter(cover, fol)
    r = list()
    for product in c:
        w = list()
        for x in keys:
            a = px[x]['a']
            b = px[x]['b']
            a = product[a]
            b = product[b]
            tyh._check_type_hint(a, b, fol.vars[x], x)
            # can `x` be ignored ?
            if use_dom:
                dom = fol.vars[x]['dom']
                a, b = tyh._clip_subrange((a, b), dom, x)
            if a is None and b is None:
                continue
            if a == b:
                s = '({x} = {a})'
            elif simple:
                s = '({a} <= {x}) /\ ({x} <= {b})'
            else:
                # precise even in absence of limits/dom
                s = '({x} \in {a} .. {b})'
            s = s.format(x=x, a=a, b=b)
            w.append(s)
        # conjoin as one triplet per line
        lines = w
        width = 3
        k = len(lines)
        n_tail = k % width
        up_to = k - n_tail
        tail = lines[up_to: k]
        lines = lines[: up_to]
        n_tail = len(tail)
        n_lines = len(lines)
        assert n_tail < width, (tail, width)
        assert n_lines % width == 0, (lines, width)
        assert (n_lines + n_tail) == k, (lines, tail)
        i = iter(lines)
        pack = width * [i]
        tuples = list(zip(*pack))
        if tail:
            tuples.append(tail)
        lines = [' /\ '.join(t) for t in tuples]
        s = stx.vertical_op(lines, latex=latex, op='and')
        r.append(s)
    r = natsort.natsorted(r)  # reproducible vertical listing
    return r


def _orthotopes_iter(u, fol):
    """Return iterator over orthotopes."""
    if u == fol.false:
        log.info('empty set')
    c = fol.pick_iter(u)
    return c


def setup_aux_vars(f, care, fol):
    """Add and return auxiliary variables.

    No BDD operations other than `support` are invoked.

    Returns:

    - `x_vars`: set of variable names in
        `support(f) \/ support(care)`
    - `px`: map var name to `dict` of indexed parameters
    - `qx`: similar for var copies
    - `p_to_q`: `dict` that maps parameters to their copies

    For example:

    ```
    x_vars = {'x', 'y'}
    px = dict(
        x=dict(a='a_x', b='b_x'),
        y=dict(a='a_y', b='b_y'))
    qx = dict(
        x=dict(a='u_x', b='v_x'),
        y=dict(a='u_y', b='v_y'))
    p_to_q = dict(
        a_x='u_x', b_x='v_x',
        a_y='u_y', b_y='v_y')
    ```

    @return x_vars, px, qx, p_to_q
    """
    assert f != fol.false
    assert care != fol.false
    assert not (f == fol.true and care == fol.true)
    x_vars = joint_support([f, care], fol)
    assert x_vars, x_vars
    # aux vars for orthotope representation
    params = dict(pa='a', pb='b', qa='u', qb='v')
    p_dom = _parameter_table(
        x_vars, fol.vars,
        a_name=params['pa'], b_name=params['pb'])
    q_dom = _parameter_table(
        x_vars, fol.vars,
        a_name=params['qa'], b_name=params['qb'])
    p_dom = stx._add_prime_like_too(p_dom)
    q_dom = stx._add_prime_like_too(q_dom)
    common = x_vars.intersection(p_dom)
    assert not common, common
    common = x_vars.intersection(q_dom)
    assert not common, common
    # works for primed variables too
    fol.declare(**p_dom)
    fol.declare(**q_dom)
    px = _map_vars_to_parameters(
        x_vars, a_name=params['pa'], b_name=params['pb'])
    qx = _map_vars_to_parameters(
        x_vars, a_name=params['qa'], b_name=params['qb'])
    assert set(px) == set(qx), (px, qx)
    p_to_q = _renaming_between_parameters(px, qx)
    q_to_p = {v: k for k, v in p_to_q.items()}
    p_to_u = {p: stx._prime_like(p) for p in p_to_q}
    p_vars = set(p_to_q)
    q_vars = set(p_to_q.values())
    u_vars = set(p_to_u.values())
    log.debug('x vars: {x_vars}'.format(x_vars=x_vars))
    assert not (p_vars & q_vars), (p_vars, q_vars)
    assert not (p_vars & u_vars), (p_vars, u_vars)
    assert not (u_vars & q_vars), (u_vars, q_vars)
    varmap = parameter_varmap(px, qx)
    # package
    prm = Parameters()
    prm._px = px
    prm._qx = qx
    prm._varmap = varmap
    prm.x_vars = x_vars
    prm.p_vars = p_vars
    prm.q_vars = q_vars
    prm.u_vars = u_vars
    prm.p_to_q = p_to_q
    prm.q_to_p = q_to_p
    prm.p_to_u = p_to_u
    return prm


def setup_lattice(prm, fol):
    """Store the lattice BDDs in `prm`."""
    log.info('partial order')
    u_leq_p, p_leq_u = partial_order(prm._px, fol)
    log.info('subseteq')
    p_leq_q = subseteq(prm._varmap, fol)
    log.info('eq')
    p_eq_q = eq(prm._varmap, fol)
    pq_vars = prm.p_vars.union(prm.q_vars)
    assert support_issubset(p_leq_q, pq_vars, fol)
    prm.u_leq_p = u_leq_p
    prm.p_leq_u = p_leq_u
    prm.p_leq_q = p_leq_q
    prm.p_eq_q = p_eq_q


def _parameter_table(x, table, a_name, b_name):
    """Return symbol table that defines parameters.

    Supports integer-valued variables only.
    Represent Boolean-valued as 0..1-valued variables.
    """
    assert x, x
    d = dict()
    for xj in x:
        dtype = table[xj]['type']
        assert dtype in ('int', 'saturating'), dtype
        dom = table[xj]['dom']
        name = stx._replace_prime(xj)
        aj = '{a}_{v}'.format(a=a_name, v=name)
        bj = '{b}_{v}'.format(b=b_name, v=name)
        d[aj] = tuple(dom)
        d[bj] = tuple(dom)
        assert "'" not in aj, aj
        assert "'" not in bj, bj
    assert len(d) == 2 * len(x), d
    return d


def _map_vars_to_parameters(x_vars, a_name, b_name):
    """Return `dict` that maps each var x to a_x, b_x."""
    d = dict()
    for x in x_vars:
        name = stx._replace_prime(x)
        a_x = '{a}_{v}'.format(a=a_name, v=name)
        b_x = '{b}_{v}'.format(b=b_name, v=name)
        d[x] = dict(a=a_x, b=b_x)
    return d


def _map_parameters_to_vars(px):
    """Return map `{a: x, b: x, ...}`."""
    d = {d['a']: k for k, d in px.items()}
    d.update((d['b'], k) for k, d in px.items())
    return d


def collect_parameters(px):
    """Return `set` of parameters from `px`."""
    c = set()
    c.update(d['a'] for d in px.values())
    c.update(d['b'] for d in px.values())
    assert len(c) == 2 * len(px), (c, px)
    return c


def parameter_varmap(px, qx):
    """Return map `{(a, b): (u, v), ... }`."""
    assert set(px) == set(qx), (px, qx)
    d = dict()
    for x in px:
        a = px[x]['a']
        b = px[x]['b']
        u = qx[x]['a']
        v = qx[x]['b']
        d[(a, b)] = (u, v)
    return d


def _renaming_between_parameters(px, qx):
    """Return map `{a: u, b: v, ... }`."""
    assert set(px) == set(qx), (px, qx)
    d = dict()
    for x in px:
        a = px[x]['a']
        b = px[x]['b']
        u = qx[x]['a']
        v = qx[x]['b']
        d[a] = u
        d[b] = v
        assert a != b, (a, b)
        assert u != v, (u, v)
        assert a != u, (a, u)
    return d


class Parameters(object):
    """Stores parameters values and lattice definition."""

    def __init__(self):
        self._px = None
        self._qx = None
        self._varmap = None
        self.x_vars = None
        self.p_vars = None
        self.q_vars = None
        self.u_vars = None
        self.p_to_q = None
        self.q_to_p = None
        self.p_to_u = None
        self.u_leq_p = None
        self.p_leq_u = None
        self.p_leq_q = None
        self.p_eq_q = None
