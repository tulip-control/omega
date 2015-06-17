"""Syntactic check for GR(1) fragment."""
from __future__ import absolute_import
import networkx as nx
from omega.logic import lexyacc
from omega.symbolic import symbolic
from omega.logic import transformation as tx


parser = lexyacc.Parser()


def ltl_to_automaton(f):
    """Return `Automaton` from LTL formula `f` as `str`.

    Formula `f` must be in the form:

      A -> G

    where each of A, G is a conjunction of terms: `B`, `[]C`, `[]<>B`.
    For more details on `B, C`, see `split_gr1`.

    @type f: `str`
    @rtype: `symbolic.Automaton`
    """
    t = parser.parse(f)
    assert t.operator == '->'
    env, sys = t.operands
    d = {'assume': split_gr1(env),
         'assert': split_gr1(sys)}
    a = symbolic.Automaton()
    a.init['env'] = d['assume']['init']
    a.init['sys'] = d['assert']['init']
    a.action['env'] = d['assume']['G']
    a.action['sys'] = d['assert']['G']
    a.win['env'] = d['assume']['GF']
    a.win['sys'] = d['assert']['GF']
    return a


def split_gr1(f):
    """Return `dict` of GR(1) subformulae.

    The formula `f` is assumed to be a conjunction of expressions
    of the form:
      `B`, `[]C` or `[]<>B`
    where:
      - `C` can contain "next"
      - `B` cannot contain "next"

    @param f: temporal logic formula
    @type f: `str` or AST

    @return: conjunctions of formulae A, B as `str`, grouped by keys:
        `'init', 'G', 'GF'`
    @rtype: `dict` of `str`: `list` of `str`
    """
    # TODO: preprocess by applying syntactic identities: [][] = [] etc
    try:
        f + 's'
        t = parser.parse(f)
    except TypeError:
        t = f
    g = tx.Tree.from_recursive_ast(t)
    # collect boundary of conjunction operators
    Q = [g.root]
    b = list()  # use lists to preserve as much given syntactic order
    while Q:
        u = Q.pop()
        # terminal ?
        if not g.succ.get(u):
            b.append(u)
            continue
        # operator
        if u.operator == '&':
            # use `u.operands` instead of `g.successors`
            # to preserve original order
            Q.extend(u.operands)
        else:
            b.append(u)
    d = {'init': list(), 'G': list(), 'GF': list()}
    for u in b:
        # terminal ?
        if not g.succ.get(u):
            d['init'].append(u)
            continue
        # some operator
        if u.operator != 'G':
            d['init'].append(u)
            continue
        # G
        (v,) = u.operands
        # terminal in G ?
        if not g.succ.get(v):
            d['G'].append(v)
            continue
        # some operator in G
        if v.operator == 'F':
            (w,) = v.operands
            d['GF'].append(w)
        else:
            # not a GF
            d['G'].append(v)
    # assert only admissible temporal operators
    ops = {'G', 'F', 'U', 'V', 'R'}
    operators = {'G': ops}
    ops = set(ops)
    ops.add('X')
    operators.update(init=ops, GF=ops)
    for part, f in d.iteritems():
        ops = operators[part]
        for u in f:
            op = has_operator(u, g, ops)
            if op is None:
                continue
            raise AssertionError((
                'found inadmissible operator "{op}" '
                'in "{f}" formula. parts:\n {d}').format(
                    op=op, f=part, d=d))
    # conjoin (except for progress)
    init = ' & '.join(u.flatten() for u in reversed(d['init']))
    d['init'] = [init]
    safe = ' & '.join(u.flatten() for u in reversed(d['G']))
    d['G'] = [safe]
    # flatten individual progress formulae
    d['GF'] = [u.flatten() for u in d['GF']]
    return d


def has_operator(u, g, operators):
    """Return `True` if AST `u` contains any `operators`."""
    try:
        if u.operator in operators:
            return u.operator
    except AttributeError:
        pass
    for v in nx.descendants(g, u):
        # terminal
        if not g.succ.get(v):
            continue
        # operator
        # is it temporal except for 'X' ?
        if v.operator in operators:
            return v.operator
    return None
