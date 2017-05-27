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


def _partial_order(px, fol):
    """Return `u <= p` and `p <= u`."""
    ux = {
        x: dict(
            a=stx._prime_like(d['a']),
            b=stx._prime_like(d['b']))
        for x, d in px.items()}
    varmap = _parameter_varmap(ux, px)
    u_leq_p = _orthotope_subseteq(varmap, fol)
    varmap = _parameter_varmap(px, ux)
    p_leq_u = _orthotope_subseteq(varmap, fol)
    return u_leq_p, p_leq_u


def essential_orthotopes(f, px, qx, fol, xvars):
    """Return essential prime orthotopes of `f`."""
    log.info('---- essential orthotopes ----')
    varmap = _parameter_varmap(px, qx)
    p_leq_q = _orthotope_subseteq(varmap, fol)
    p_eq_q = _orthotope_eq(varmap, fol)
    p_is_prime = prime_orthotopes(
        f, px, qx,
        p_leq_q, p_eq_q,
        fol, xvars)
    # add to quantify u, v, so that we can rename
    #
    # TODO: reimplement using `fol.Context.rename`
    varmap = _parameter_varmap(qx, px)
    q_leq_p = _orthotope_subseteq(varmap, fol)
    q_is_prime = prime_orthotopes(
        f, qx, px,
        q_leq_p, p_eq_q,
        fol, xvars)
    x_in_q = _orthotope_contains_x(qx, fol)
    x = ', '.join(px)
    q = ', '.join(_collect_parameters(qx))
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
            p_eq_q=p_eq_q,
            x_in_q=x_in_q,
            f=f, x=x, q=q)
    r = fol.add_expr(s)
    log.info('==== essential orthotopes ====')
    return r


def prime_orthotopes(
        f, px, qx,
        p_leq_q, p_eq_q,
        fol, xvars):
    """Return dominators of implicants."""
    log.info('----- prime orthotopes ----')
    assert support_issubset(f, xvars, fol)
    p_to_q = _renaming_between_parameters(px, qx)
    p_is_implicant = _implicant_orthotopes(f, px, fol, xvars)
    q_is_implicant = fol.let(p_to_q, p_is_implicant)
    q = _collect_parameters(qx)
    r = q_is_implicant & p_leq_q
    r = p_eq_q | ~ r
    r = fol.forall(q, r)
    r &= p_is_implicant
    '''
    q = ', '.join(_collect_parameters(qx))
    s = (
        '{p_is_implicant} /\ '
        r'\A {q}:  ( '
        '     ({q_is_implicant} /\ {p_leq_q})'
        '     => {p_eq_q}'
        ')').format(
            p_is_implicant=p_is_implicant,
            q_is_implicant=q_is_implicant,
            p_leq_q=p_leq_q,
            p_eq_q=p_eq_q,
            q=q)
    r = fol.add_expr(s)
    '''
    log.info('==== prime orthotopes ====')
    return r


def _implicant_orthotopes(f, abx, fol, xvars):
    """Return orthotopes that imply `f`.

    Caution: `fol` type hints are ignored.
    """
    log.info('---- implicant orthotopes ----')
    assert support_issubset(f, xvars, fol)
    x = ', '.join(abx)
    h = _orthotope_contains_x(abx, fol)
    nonempty = _orthotope_nonempty(abx, fol)
    s = (
        '{nonempty} /\ '
        '\A {x}:  {h} => {f} ').format(
            x=x, h=h, f=f, nonempty=nonempty)
    r = fol.add_expr(s)
    log.info('==== implicant orthotopes ====')
    return r


def _embed_as_implicants(f, px, fol):
    ax = {x: d['a'] for x, d in px.items()}
    bx = {x: d['b'] for x, d in px.items()}
    u = fol.let(ax, f)
    v = _orthotope_singleton(px, fol)
    return u & v


def _embed_as_implicants_naive(f, px, fol):
    """Return product representation of minterms."""
    x_as_ab = {x: dict(a=x, b=x) for x in px}
    varmap = _parameter_varmap(px, x_as_ab)
    r = _orthotope_eq(varmap, fol)
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


def _orthotope_contains_x(abx, fol):
    """Return `x \in concretization(abx)`."""
    s = stx.conj((
        '({a} <= {x}) /\ '
        '({x} <= {b})').format(
            x=x, a=d['a'], b=d['b'])
        for x, d in abx.items())
    r = fol.add_expr(s)
    return r


def _orthotope_subseteq(varmap, fol):
    r"""Return `ab \subseteq uv`.

    This is the partial order defined by the subset relation.
    In the general formulation `\sqsubseteq`.
    """
    s = stx.conj((
        '({u} <= {a}) /\ '
        '({b} <= {v})').format(a=a, b=b, u=u, v=v)
            for (a, b), (u, v) in varmap.items())
    r = fol.add_expr(s)
    return r


def _orthotope_eq(varmap, fol):
    """Return `ab = uv`."""
    s = stx.conj((
        '({a} = {u}) /\ '
        '({b} = {v})').format(a=a, b=b, u=u, v=v)
        for (a, b), (u, v) in varmap.items())
    r = fol.add_expr(s)
    return r


def _orthotopes_intersect(varmap, fol):
    """Return `ab \cap uv # \emptyset`.

    Equivalent to

    \E x:  /\ x \in concretization(ab)
           /\ x \in concretization(uv)

    The representation of orthotopes as products of
    intervals allows for a direct construction that
    avoids quantification over `x`.
    """
    # disjoint intervals in at least one dimension
    s = stx.disj((
        '({b} < {u}) \/ '
        '({v} < {a})').format(a=a, b=b, u=u, v=v)
            for (a, b), (u, v) in varmap.items())
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


def _list_orthotope_expr(
        cover, px, fol,
        simple=False,
        use_dom=False):
    """Return `list` of `str`, each an orthotope in `cover`.

    @param simple: if `True`, then return expression
        that can be parsed by `fol.add_expr`.
    @param use_dom: omit conjuncts that contain dom of var
        assumes that `|= care => type_hints`
    """
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
            _check_type_hint(a, b, fol.vars[x], x)
            # can `x` be ignored ?
            if use_dom:
                dom = fol.vars[x]['dom']
                a, b = _clip_subrange((a, b), dom, x)
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
        s = ' /\ '.join(w)
        if not s:
            s = 'TRUE'
        r.append(s)
    r = natsort.natsorted(r)  # reproducible vertical listing
    return r


def _orthotopes_iter(u, fol):
    """Return iterator over orthotopes."""
    if u == fol.false:
        log.info('empty set')
    c = fol.pick_iter(u)
    return c


def _setup_aux_vars(f, care, fol):
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
        x_vars, fol.vars, a=params['pa'], b=params['pb'])
    q_dom = _parameter_table(
        x_vars, fol.vars, a=params['qa'], b=params['qb'])
    p_dom = stx._add_prime_like_too(p_dom)
    q_dom = stx._add_prime_like_too(q_dom)
    common = x_vars.intersection(p_dom)
    assert not common, common
    common = x_vars.intersection(q_dom)
    assert not common, common
    # works for primed variables too
    fol.declare(**p_dom)
    fol.declare(**q_dom)
    px = _parameter_variables(x_vars, a=params['pa'], b=params['pb'])
    qx = _parameter_variables(x_vars, a=params['qa'], b=params['qb'])
    assert set(px) == set(qx), (px, qx)
    p_to_q = _renaming_between_parameters(px, qx)
    log.debug('x vars: {x_vars}'.format(x_vars=x_vars))
    return x_vars, px, qx, p_to_q


def _parameter_table(x, table, a, b):
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
        aj = '{a}_{v}'.format(a=a, v=name)
        bj = '{b}_{v}'.format(b=b, v=name)
        d[aj] = dom
        d[bj] = dom
        assert "'" not in aj, aj
        assert "'" not in bj, bj
    assert len(d) == 2 * len(x), d
    return d


def _parameter_variables(x_vars, a, b):
    """Return `dict` that maps each var x to a_x, b_x."""
    d = dict()
    for x in x_vars:
        name = stx._replace_prime(x)
        a_x = '{a}_{v}'.format(v=name, a=a)
        b_x = '{b}_{v}'.format(v=name, b=b)
        d[x] = dict(a=a_x, b=b_x)
    return d


def _map_parameters_to_vars(px):
    """Return map `{a: x, b: x, ...}`."""
    d = {d['a']: k for k, d in px.items()}
    d.update((d['b'], k) for k, d in px.items())
    return d


def _collect_parameters(px):
    """Return `set` of parameters from `px`."""
    c = set()
    c.update(d['a'] for d in px.values())
    c.update(d['b'] for d in px.values())
    assert len(c) == 2 * len(px), (c, px)
    return c


def _parameter_varmap(px, qx):
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
    return d
