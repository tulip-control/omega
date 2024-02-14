"""Translation of past to future LTL.


References
==========

Orna Lichtenstein, Amir Pnueli, Lenore Zuck
    "The glory of the past"
    Conf. on Logics of Programs
    LNCS Vol.193, pp.196--218, 1985

Zohar Manna, Amir Pnueli
    "The anchored version of the temporal framework"
    Linear time, branching time and partial order in
    logics and models of concurrency
    LNCS Vol.354, pp.201--284

Yonit Kesten, Amir Pnueli, Li-on Raviv
    "Algorithmic verification of linear temporal logic specifications"
    Int. Colloquium on Automata, Languages, and Programming (ICALP)
    LNCS Vol.1443, pp.1--16, 1998

Roderick Bloem, Barbara Jobstmann, Nir Piterman,
    Amir Pnueli, Yaniv Sa'ar
    "Synthesis of reactive(1) designs"
    Journal of Computer and System Sciences
    Vol.78, No.3, pp.911--938, 2012
"""
# Copyright 2015 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
import logging

from omega.logic.ast import Nodes as _Nodes
from omega.logic import lexyacc
from omega.logic.syntax import conj


logger = logging.getLogger('astutils').setLevel(logging.ERROR)


class Nodes(_Nodes):
    """LTL AST with flatteners to future LTL."""

    class Operator(_Nodes.Operator):
        def flatten(self, context=None, *arg, **kw):
            # ite both function and connective
            if self.operator == 'ite':
                x, y, z = self.operands
                a = x.flatten(context='bool', *arg, **kw)
                b = y.flatten(context=context, *arg, **kw)
                c = z.flatten(context=context, *arg, **kw)
                return ''.join([
                    self.operator,
                    '(',
                    ', '.join((a, b, c)),
                    ')'])
            if self.operator == '@':
                x, = self.operands
                return '@' + x.flatten(context=context, *arg, **kw)
            return super().flatten(
                context=context, *arg, **kw)

    class Unary(_Nodes.Unary):
        def flatten(self, *arg, **kw):
            # type checking
            c = kw.get('context')
            until = kw.get('until')
            # recurse
            op = self.operator
            if op in ('-X', '--X'):
                x = self.operands[0]
                return _flatten_previous(op, x, *arg, **kw)
            if op != 'X':
                assert c == 'bool', (c, op)
            if op == '-[]':
                x = Nodes.Bool('TRUE')
                y = Nodes.Unary('~', self.operands[0])
                a = (x, y)
                r = _flatten_since(a, *arg, **kw)
                return f'(~ {r})'
            elif op == '-<>':
                a = (Nodes.Bool('TRUE'), self.operands[0])
                return _flatten_since(a, *arg, **kw)
            elif op == '[]' and until:
                x = Nodes.Bool('TRUE')
                y = Nodes.Unary('~', self.operands[0])
                a = (x, y)
                r = _flatten_until(a, *arg, **kw)
                return f'(~ {r})'
            elif op == '<>' and until:
                a = (Nodes.Bool('TRUE'), self.operands[0])
                return _flatten_until(a, *arg, **kw)
            return super().flatten(*arg, **kw)

    class Binary(_Nodes.Binary):
        def flatten(self, *arg, **kw):
            # type checking
            c = kw.get('context')
            assert c == 'bool', c
            until = kw.get('until')
            # recurse
            op = self.operator
            if op == 'S':
                return _flatten_since(
                    self.operands, *arg, **kw)
            elif op == 'U' and until:
                return _flatten_until(
                    self.operands, *arg, **kw)
            return super().flatten(*arg, **kw)

    class Comparator(_Nodes.Comparator):
        def flatten(self, *arg, **kw):
            # type checking
            c = kw.get('context')
            assert c == 'bool', (c, str(self))
            # change context
            kw['context'] = 'arithmetic'
            # recurse
            return super().flatten(*arg, **kw)

    class Arithmetic(_Nodes.Arithmetic):
        def flatten(self, *arg, **kw):
            # type checking
            c = kw.get('context')
            assert c == 'arithmetic', c
            # change context
            kw['context'] = 'arithmetic'
            # recurse
            return super().flatten(*arg, **kw)

    class Var(_Nodes.Var):
        def flatten(self, testers=None, context=None,
                    previous=None, strong=None, free_init=None,
                    *arg, **kw):
            var = self.value
            if previous is None:
                return var
            # previous N
            assert testers is not None
            assert context == 'bool', (context, self.value)
            previous + 1  # isinstance(previous, int)  ?
            var_prev = f'{var}_prev{previous}'
            # add tester
            init, trans = _make_tester_for_previous(
                var_prev, var, context, strong)
            testers[var_prev] = dict(
                type='bool',  # previous applies only to bool vars
                init=init, trans=trans, win=None)
            return var_prev


def _flatten_previous(op, x, testers, context,
                      previous=0, strong=None, *arg, **kw):
    """Translate expression with "previous" as main operator."""
    # propagate ?
    # (if child is terminal)
    # added benefit: shares some history vars among subformulas
    strong = (op == '--X')
    propagate = (
        len(x) == 1)
    if propagate:
        previous += 1
        return x.flatten(testers=testers, context=context,
                         previous=previous, strong=strong, *arg, **kw)
    # create tester here
    assert context == 'bool', context
    assert len(x) > 1, 'operand is an operator'
    expr = x.flatten(testers=testers, context=context, *arg, **kw)
    # bottom-up counting is safe
    # `len` *must* be called after `flatten`
    # note that each `x_prev` occupies an "aux" index
    i = len(testers)
    var_prev = f'_aux{i}'
    # create tester
    init, trans = _make_tester_for_previous(
        var_prev, expr, context, strong)
    testers[var_prev] = dict(
        type='bool',
        init=init, trans=trans, win=None)
    return var_prev


def _make_tester_for_previous(var, expr, context, strong):
    """Return temporal tester for "previous"."""
    # select operator
    if context == 'bool':
        op = '<=>'
        # strong "previous" operator "--X" ?
        if strong:
            init = f'(~ {var})'
        else:
            init = var
    else:
        raise Exception(
            f'unknown context: "{context}"')
    # translate "previous" in future LTL
    trans = f"(({var}') {op} {expr})"
    return init, trans


def _flatten_since(operands, testers, context, *arg, **kw):
    """Translate expression with "since" as main operator."""
    assert context == 'bool', context
    x, y = operands
    p = x.flatten(testers=testers, context=context, *arg, **kw)
    q = y.flatten(testers=testers, context=context, *arg, **kw)
    i = len(testers)
    var = f'_aux{i}'
    init = f'({var} <=> {q})'
    trans = rf'''
        (
        ({var}') <=> (
            ({q}') \/ (({p}') /\ {var})
        ))
        '''
    testers[var] = dict(
        type='bool',
        init=init, trans=trans, win=None)
    return var


def _flatten_until(operands, testers, context, *arg, **kw):
    assert context == 'bool', context
    x, y = operands
    p = x.flatten(testers=testers, context=context, *arg, **kw)
    q = y.flatten(testers=testers, context=context, *arg, **kw)
    i = len(testers)
    var = f'_aux{i}'
    trans = rf'''
        (
        {var} <=> (
            ({q}) \/ (({p}) /\ ({var}'))
        ))
        '''
    win = rf'(({q}) \/ ~ {var})'
    testers[var] = dict(
        type='bool',
        init='TRUE', trans=trans, win=win)
    return var


# LTL parser that translates past to future.
parser = lexyacc.Parser(nodes=Nodes)


def translate(s, debug=False, until=False):
    """Translate action formula `s` with past to future LTL.

    Return:
      - history and prophecy variable symbol table
      - translated formula
      - initial condition of temportal testers
      - conjunction `c` of translated formula with
        transition relations of temporal testers.
      - list of recurrence goals

    If formula `s` is an action (in the sense of TLA),
    then the returned formula `c` is also an action.

    Note that if two subformulas are identical,
    then a fresh variable will be used for each one.
    The only exception are variables, for example "-X p".

    @type s:
        `str`
    @param debug:
        ensures repeatable ordering
        of new subformulas, to enable testing.
    @param until:
        add prophecy variables for "until" too
    @return:
        `(dvars, translated, init, action)`
    @rtype:
        `tuple`
    """
    tree = parser.parse(s)
    testers = dict()
    context = 'bool'
    r = tree.flatten(testers=testers, context=context,
                     until=until)
    if debug:
        ci = sorted(d['init'] for d in testers.values())
        ct = sorted(d['trans'] for d in testers.values())
        win = [d['win'] for d in testers.values()
               if d['win'] is not None]
    else:
        ci = (d['init'] for d in testers.values())
        ct = (d['trans'] for d in testers.values())
        win = [d['win'] for d in testers.values()
               if d['win'] is not None]
    init = conj(ci)
    trans = conj(ct)
    # collect new vars
    dvars = dict()
    for var_prev, d in testers.items():
        dtype = d['type']
        dom = d.get('dom')
        dvars[var_prev] = dict(type=dtype, dom=dom, owner='sys')
    return dvars, r, init, trans, win


def map_translate(c, **kw):
    """Apply `translate` to all items of container `c`."""
    all_vars = dict()
    f = list()
    init = list()
    action = list()
    win = list()
    for s in c:
        dvars, r, i, a, w = translate(s, **kw)
        all_vars.update(dvars)
        f.append(r)
        init.append(i)
        action.append(a)
        win.extend(w)
    return all_vars, f, init, action, win
