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
                a = x.flatten(context='boolean', *arg, **kw)
                b = y.flatten(context=context, *arg, **kw)
                c = z.flatten(context=context, *arg, **kw)
                return ''.join([
                    self.operator,
                    '(',
                    ', '.join((a, b, c)),
                    ')'])
            return super(Nodes.Operator, self).flatten(
                context=context, *arg, **kw)

    class Unary(_Nodes.Unary):
        def flatten(self, *arg, **kw):
            # type checking
            c = kw.get('context')
            # recurse
            if self.operator in ('-X', '--X'):
                x = self.operands[0]
                return _flatten_previous(self.operator, x, *arg, **kw)
            if self.operator != 'X':
                assert c == 'boolean', (c, self.operator)
            if self.operator == '-[]':
                x = Nodes.Bool('True')
                y = Nodes.Unary('!', self.operands[0])
                c = (x, y)
                r = _flatten_since(c, *arg, **kw)
                return '(! {r})'.format(r=r)
            elif self.operator == '-<>':
                c = (Nodes.Bool('True'), self.operands[0])
                return _flatten_since(c, *arg, **kw)
            return super(Nodes.Unary, self).flatten(*arg, **kw)

    class Binary(_Nodes.Binary):
        def flatten(self, *arg, **kw):
            # type checking
            c = kw.get('context')
            assert c == 'boolean', c
            # recurse
            if self.operator == 'S':
                return _flatten_since(
                    self.operands, *arg, **kw)
            return super(Nodes.Binary, self).flatten(*arg, **kw)

    class Comparator(_Nodes.Comparator):
        def flatten(self, *arg, **kw):
            # type checking
            c = kw.get('context')
            assert c == 'boolean', (c, str(self))
            # change context
            kw['context'] = 'arithmetic'
            # recurse
            return super(Nodes.Comparator, self).flatten(*arg, **kw)

    class Arithmetic(_Nodes.Arithmetic):
        def flatten(self, *arg, **kw):
            # type checking
            c = kw.get('context')
            assert c == 'arithmetic', c
            # change context
            kw['context'] = 'arithmetic'
            # recurse
            return super(Nodes.Arithmetic, self).flatten(*arg, **kw)

    class Var(_Nodes.Var):
        def flatten(self, testers=None, context=None,
                    previous=None, strong=None, free_init=None,
                    *arg, **kw):
            if previous is None:
                return self.value
            # previous N
            assert testers is not None
            assert context is not None
            previous + 1  # isinstance(previous, int)  ?
            var = self.value
            var_prev = '{name}_prev{i}'.format(
                name=var, i=previous)
            dtype = var
            # add tester
            init, trans = _make_tester_for_previous(
                var_prev, var, context, strong)
            # unconstrained init ?
            if free_init is not None and var in free_init:
                init = 'True'
            testers[var_prev] = dict(
                init=init, trans=trans, type=dtype)
            return var_prev


def _flatten_previous(op, x, testers, context,
                      previous=0, strong=None, *arg, **kw):
    """Translate expression with "previous" as main operator."""
    # propagate ?
    # (if arithmetic context or child is terminal)
    # added benefit: avoids unnecessary constant aux vars
    strong = (op == '--X')
    propagate = (
        context == 'arithmetic' or
        len(x) == 1 or
        (len(x) == 2 and x.operator in ('-X', '--X')))
    if propagate:
        previous += 1
        return x.flatten(testers=testers, context=context,
                         previous=previous, strong=strong, *arg, **kw)
    # create tester here
    assert context == 'boolean', context
    assert len(x) > 1, 'operand is an operator'
    expr = x.flatten(testers=testers, context=context, *arg, **kw)
    # bottom-up counting is safe
    # `len` *must* be called after `flatten`
    # note that each `x_prev` occupies an "aux" index
    i = len(testers)
    var_prev = '_aux{i}'.format(i=i)
    # create tester
    init, trans = _make_tester_for_previous(
        var_prev, expr, context, strong)
    testers[var_prev] = dict(init=init, trans=trans, type='bool')
    return var_prev


def _make_tester_for_previous(var, expr, context, strong):
    """Return temporal tester for "previous"."""
    # select operator
    if context == 'boolean':
        op = '<->'
        # strong "previous" operator "--X" ?
        if strong:
            init = '(! {var})'.format(var=var)
        else:
            init = var
    elif context == 'arithmetic':
        print('warning: an experiment, remember to init aux var')
        assert not strong
        op = '='
        # init for weak "previous"
        init = 'True'
    else:
        raise Exception(
            'unknown context: "{c}"'.format(c=context))
    # translate "previous" in future LTL
    trans = '((X {var}) {op} {expr})'.format(
        var=var, op=op, expr=expr)
    return init, trans


def _flatten_since(operands, testers, context, *arg, **kw):
    """Translate expression with "since" as main operator."""
    assert context == 'boolean', context
    x, y = operands
    p = x.flatten(testers=testers, context=context, *arg, **kw)
    q = y.flatten(testers=testers, context=context, *arg, **kw)
    i = len(testers)
    var = '_aux{i}'.format(i=i)
    init = '({var} <-> {q})'.format(var=var, q=q)
    trans = (
        '('
        '(X {var}) <-> ('
        '(X {q}) | ((X {p}) & {var})'
        '))').format(
            var=var, p=p, q=q)
    testers[var] = dict(init=init, trans=trans, type='bool')
    return var


class Parser(lexyacc.Parser):
    """LTL parser that translates past to future."""

    nodes = Nodes


parser = Parser()


def translate(s, t, free_init=None, debug=False):
    """Translate full LTL formula `s` to future LTL.

    Return:
      - initial condition of temportal testers
      - conjunction `c` of translated formula with
        transition relations of temporal testers.

    If formula `s` is an action (in the sense of TLA),
    then the returned formula `c` is also an action.

    Note that if two subformulae are identical,
    then a fresh variable will be used for each one.
    The only exception are variables, for example "-X p".

    @type s: `str`
    @param t: symbol table
    @type t: `dict`
    @param free_init: variables with unconstrained anchor
    @type free_init: `set`
    @param debug: ensures repeatable ordering
        of new subformulas, to enable testing.
    @return: `(dvars, init, future_s)`
    @rtype: `tuple`
    """
    tree = parser.parse(s)
    testers = dict()
    context = 'boolean'
    r = tree.flatten(testers=testers, context=context,
                     free_init=free_init)
    if debug:
        ci = sorted(d['init'] for d in testers.itervalues())
        ct = sorted(d['trans'] for d in testers.itervalues())
    else:
        ci = (d['init'] for d in testers.itervalues())
        ct = (d['trans'] for d in testers.itervalues())
    init = conj(ci)
    trans = conj(ct)
    trans = conj([r, trans])
    # collect new vars
    dvars = dict()
    for var_prev, d in testers.iteritems():
        dtype = d['type']
        # get type from base variable
        # (for example, base var of "-X p" is "p")
        if dtype == 'bool':
            dom = None
        elif dtype in t:
            var = dtype
            q = t[var]
            dtype = q['type']
            dom = q.get('dom')
        else:
            raise Exception(
                'variable "{var}" missing from table {t}.'.format(
                    var=dtype, t=t))
        dvars[var_prev] = dict(type=dtype, dom=dom, owner='sys')
    return dvars, init, trans


def map_translate(c, t, **kw):
    """Apply `translate` to all items of container `c`."""
    add_vars = dict()
    add_init = list()
    add_action = list()
    for s in c:
        dvars, init, action = translate(s, t, **kw)
        add_vars.update(dvars)
        add_init.append(init)
        add_action.append(action)
    return add_vars, add_init, add_action
