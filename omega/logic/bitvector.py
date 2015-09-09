"""Bit-blasting for signed integer arithmetic.

This module translates Boolean formulas that can
contain arithmetic expressions involving signed integers
to bitvector propositional formulas.

Reference
=========

Chapter 6, in particular pp. 158--159 from:
Kroening D. and Strichman O.
Decision Procedures, Springer
"""
from __future__ import absolute_import
import logging
import math
import networkx as nx
from omega.logic import lexyacc
from omega.logic.ast import Nodes as _Nodes


ALU_BITWIDTH = 32
logger = logging.getLogger(__name__)


def bitblast(f, t):
    """Flatten formula `f` to bitvector logic.

    @param f: unquantified first-order temporal logic formula
    @type f: `str`
    @param t: symbol table
    @type t: `dict`
    """
    tree = _parser.parse(f)
    return tree.flatten(t=t)


def bitblast_table(table):
    """Return table of variables for bitvectors.

    `table` is a `dict` that maps each variable
    to a `dict` with attributes:

      - "type": `in ('bool', 'saturating', 'modwrap', 'int')`
      - "owner": `in ('env', 'sys')`
      - "dom": `tuple([min, max])` where `min, max` are `int`
        used only if "type" is an integer
      - "init" (optional)
    """
    data_types = {'bool', 'int', 'saturating', 'modwrap'}
    t = dict()
    init = {'env': list(), 'sys': list()}
    safety = {'env': list(), 'sys': list()}
    keys = {'type', 'owner', 'dom', 'signed',
            'width', 'bitnames', 'init'}
    for var, d in table.iteritems():
        dtype = d['type']
        owner = d['owner']
        assert dtype in data_types, (var, dtype)
        b = dict(d)  # cp other keys
        for k in keys:
            b.pop(k, None)
        if dtype == 'bool':
            b.update(type='bool', owner=owner)
        elif dtype in ('saturating', 'modwrap', 'int'):
            dom = d['dom']
            assert len(dom) == 2, dom
            signed, width = dom_to_width(dom)
            b.update(type='int', owner=owner,
                     signed=signed, width=width,
                     dom=dom)
        else:
            raise Exception(
                'unknown type: "{dtype}"'.format(dtype=dtype))
        if dtype == 'int':
            print('WARNING: "int" found as type '
                  '(instead of "saturating")')
        t[var] = b
        # initial value
        # imperative var or free var assigned at decl ?
        ival = d.get('init')
        if ival is not None:
            c = _init_to_logic(var, d)
            init[owner].append(c)
        # ranged bitfield safety constraints
        if dtype == 'bool':
            continue
        # int var
        assert dtype in ('int', 'saturating', 'modwrap')
        dmin, dmax = dom
        # saturating semantics ?
        if dtype not in ('saturating', 'int'):
            # must range between powers of two
            v = abs(dmin) + 1
            assert not (v & (v - 1)), (var, dmin)
            v = abs(dmax) + 1
            assert not (v & (v - 1)), (var, dmax)
            continue
        # still included, for use with counters
        # during transducer construction,
        # because closure not taken for the counters
        init[owner].append(
             '({min} <= {x}) & ({x} <= {max})'.format(
                 min=dmin, max=dmax, x=var))
        # prime needed to enforce limits now, not one step later,
        # otherwise env can violate limits, if that will force
        # sys to lose in the next time step.
        safety[owner].append((
            '({min} <= {x}) & ({x} <= {max}) & '
            '({min} <= X({x}) ) & ( X({x}) <= {max})').format(
                min=dmin, max=dmax, x=var))
    _check_data_types(t)
    _add_bitnames(t)
    logger.info('-- done bitblasting vars table\n')
    return t, init, safety


def _init_to_logic(var, d):
    """Return logic formulae for initial condition."""
    if d['type'] == 'boolean':
        op = '<->'
    else:
        op = '='
    return '{var} {op} {value}'.format(
        op=op, var=var, value=d['init'])


def dom_to_width(dom):
    """Return whether integer variable is signed and its bit width.

    @param dom: the variable's range
    @type dom: `(MIN, MAX)` where `MIN, MAX` are integers
    """
    minval, maxval = dom
    logger.debug('int in ({m}, {M})'.format(
        m=minval, M=maxval))
    signed = (minval < 0) and (maxval > 0)
    absval = max(abs(minval), abs(maxval))
    width = absval.bit_length()
    if width == 0:
        assert minval == maxval
        # TODO: optimize by substituting values
        # for variables that are constants
        width = 1
    if signed:
        width = width + 1
    return signed, width


def _add_bitnames(t):
    """Map each integer to a list of bit variables."""
    # str_to_int not needed, because there
    # are no string variables in Promela
    for var, d in t.iteritems():
        if d['type'] == 'int':
            bits = ['{name}_{i}'.format(name=var, i=i)
                    for i in xrange(d['width'])]
            are_booleans = filter(t.__contains__, bits)
            assert not are_booleans, (bits, t)
            d['bitnames'] = bits


def _check_data_types(t):
    types = {'bool', 'int'}
    for var, d in t.iteritems():
        if d['type'] in types:
            continue
        raise Exception(
            'unknown type: "{dtype}"'.format(dtype=d['type']))


def list_bits(dvars):
    """Return symbol table of bits (comprising bitfields).

    For symbol table definition, see `bitblast_table`.

    @param dvars: symbol table of integer and Boolean vars
    @type dvars: `dict` of `dict`
    @return: symbol table of bits
    @rtype: `dict` of `dict`
    """
    dout = dict()
    keys = {'type', 'owner', 'dom', 'signed',
            'width', 'bitnames', 'init'}
    for var, d in dvars.iteritems():
        dtype = d['type']
        if dtype == 'int':
            c = d['bitnames']
        elif dtype == 'bool':
            c = [var]
        else:
            raise Exception(
                'unknown type "{t}"'.format(t=dtype))
        owner = d['owner']
        assert owner in {'env', 'sys'}, owner
        dcp = dict(d)  # cp other keys
        for k in keys:
            dcp.pop(k, None)
        for bit in c:
            dbit = dict(dcp)
            dbit.update(type='bool', owner=owner)
            dout[bit] = dbit
    return dout


def bitfield_to_int_states(g, t):
    """Convert bitfields to integers for "state" at each node.

    @type g: `networkx.DiGraph`
    @type t: `VariablesTable`

    @rtype: `networkx.Digraph`
    """
    h = nx.DiGraph()
    for u, d in g.nodes_iter(data=True):
        bit_state = d['state']
        int_state = bitfields_to_ints(bit_state, t)
        h.add_node(u, state=int_state)
    for u, v in g.edges_iter():
        h.add_edge(u, v)
    assert len(g) == len(h), (len(g), len(h))
    # remove deadends, where env looses
    s = {1}
    while s:
        s = {n for n in h if not h.succ.get(n)}
        h.remove_nodes_from(s)
    assert h or not g, 'No loop in given graph `g`.'
    logger.debug(
        ('converted bitfields to integers.\n'
         'Strategy with vertices:\n  {v}\n'
         'and edges:\n {e}\n').format(
            v='\n  '.join(str(x) for x in h.nodes(data=True)),
            e=h.edges()))
    return h


def bitfields_to_ints(bit_state, t):
    """Convert bits to integer for state `dict`.

    @param bit_state: assignment to all bits
    @type bit_state: `dict`
    @type t: `VariablesTable`
    """
    int_state = dict()
    for flatname, d in t.iteritems():
        if d['type'] == 'bool':
            int_state[flatname] = bit_state[flatname]
            continue
        # this is an integer var
        bitnames = d['bitnames']
        bitvalues = [bit_state[b] for b in bitnames]
        _append_sign_bit(bitvalues, flatname, d)
        int_state[flatname] = twos_complement_to_int(bitvalues)
    return int_state


def make_table(d, env_vars=None):
    """Return symbol table from "simple" `dict`."""
    if env_vars is None:
        env_vars = set()
    t = dict()
    for var, dom in d.iteritems():
        if dom == 'bool':
            dtype = 'bool'
            dom = None
        else:
            assert isinstance(dom, tuple), (var, dom)
            assert len(dom) == 2, (var, dom)
            dtype = 'saturating'
        if var in env_vars:
            owner = 'env'
        else:
            owner = 'sys'
        t[var] = dict(type=dtype, dom=dom, owner=owner)
    return t


def make_dummy_table():
    t = dict(x=dict(type='bool', owner='env'),
             y=dict(type='bool', owner='sys'),
             z=dict(type='int', owner='env', signed=False, width=2),
             w=dict(type='int', owner='env', signed=False, width=2))
    return t


class Nodes(_Nodes):
    """Return object with AST node classes as attributes."""
    opmap = {
        'false': '0', 'true': '1',
        '!': '!',
        '|': '|', '&': '&', '->': '| !', '<->': '! ^',
        'ite': 'ite',
        'X': '',
        # 'G': '[]', 'F': '<>',
        '<': '<', '<=': '<=', '=': '=',
        '>=': '>=', '>': '>', '!=': '!=',
        '+': '+', '-': '-'}

    class Operator(_Nodes.Operator):
        def flatten(self, mem=None, *arg, **kw):
            if self.operator != 'ite':
                return super(Nodes.Operator, self).flatten(
                    mem=mem, *arg, **kw)
            # ternary conditional
            assert self.operator == 'ite'
            x = self.operands[0].flatten(mem=None, *arg, **kw)
            y = self.operands[1].flatten(mem=mem, *arg, **kw)
            z = self.operands[2].flatten(mem=mem, *arg, **kw)
            # ternary connective ?
            if mem is None:
                return ite_connective(x, y, z)
            else:
                p, q = equalize_width(y, z)
                r, ite_mem = ite_function(x, p, q, start=len(mem))
                mem.extend(ite_mem)
                return r

    class Unary(_Nodes.Unary):
        def flatten(self, *arg, **kw):
            logger.info('flatten "{s}"'.format(s=repr(self)))
            if self.operator == 'X':
                kw.update(prime=True)
                # avoid making it a string
                # (because in arithmetic context it is a list)
                return self.operands[0].flatten(*arg, **kw)
            return ' {op} {x}'.format(
                op=Nodes.opmap[self.operator],
                x=self.operands[0].flatten(*arg, **kw))

    # prefix and rm parentheses
    class Binary(_Nodes.Binary):
        def flatten(self, *arg, **kw):
            """Prefix flattener."""
            logger.info('flatten "{s}"'.format(s=repr(self)))
            x = self.operands[0].flatten(*arg, **kw)
            y = self.operands[1].flatten(*arg, **kw)
            assert isinstance(x, basestring), x
            assert isinstance(y, basestring), y
            return ' {op} {x} {y} '.format(
                op=Nodes.opmap[self.operator], x=x, y=y)

    class Var(_Nodes.Var):
        def flatten(self, prime=None, mem=None, t=None, *arg, **kw):
            logger.info('flatten "{s}"'.format(s=repr(self)))
            name = self.value
            if _is_bool_var(name, t):
                # Boolean scope ?
                if name in t:
                    assert mem is None
                return '{v}{prime}'.format(
                    v=name, prime="'" if prime else '')
            # arithmetic context
            # must be integer variable
            bits = var_to_twos_complement(name, t)
            bits = ["{b}{prime}".format(
                b=b, prime="'" if not b[0].isdigit() and prime else '')
                for b in bits]
            return bits

    class Num(_Nodes.Num):
        def flatten(self, *arg, **kw):
            logger.info('flatten "{s}"'.format(s=repr(self)))
            return int_to_twos_complement(self.value)

    class Bool(_Nodes.Bool):
        def flatten(self, *arg, **kw):
            return Nodes.opmap[self.value.lower()]

    class Comparator(_Nodes.Comparator):
        def flatten(self, mem=None, *arg, **kw):
            logger.info('flatten "{s}"'.format(s=repr(self)))
            assert mem is None, (
                '"{expr}" appears in arithmetic scope'.format(
                    expr=self))
            mem = list()
            p = self.operands[0].flatten(mem=mem, *arg, **kw)
            q = self.operands[1].flatten(mem=mem, *arg, **kw)
            return flatten_comparator(self.operator, p, q, mem)

    class Arithmetic(_Nodes.Arithmetic):
        def flatten(self, mem=None, *arg, **kw):
            if self.operator == '<<>>':
                return flatten_truncator(
                    self.operands, mem=mem, *arg, **kw)
            logger.info('flatten "{s}"'.format(s=repr(self)))
            # only for testing purposes
            assert mem is not None, (
                'Arithmetic formula "{f}" in Boolean scope.'.format(
                    f=self))
            p = self.operands[0].flatten(mem=mem, *arg, **kw)
            q = self.operands[1].flatten(mem=mem, *arg, **kw)
            return flatten_arithmetic(self.operator, p, q, mem)


_parser = lexyacc.Parser(nodes=Nodes())


def flatten_truncator(operands, mem=None, *arg, **kw):
    """Return integer truncated to given width."""
    logger.info(
        '++ flatten truncator "{s}"'.format(s=operands))
    p = operands[0].flatten(mem=mem, *arg, **kw)
    assert isinstance(p, list), p
    y = operands[1]
    assert isinstance(y, Nodes.Num), (type(y), y)
    n = int(y.value)
    tr = truncate(p, n)
    # if extended, should not use MSB of truncation
    tr.append('0')
    logger.debug('truncation result: {tr}\n'.format(tr=tr))
    logger.info('-- done flattening truncator.\n')
    return tr


def flatten_comparator(operator, x, y, mem):
    """Return flattened comparator formula."""
    logger.info(
        '++ flatten comparator "{op}" ...'.format(op=operator))
    assert isinstance(x, list)
    assert isinstance(y, list)
    p, q = equalize_width(x, y)
    assert len(p) == len(q)
    logger.debug('p = {p}\nq = {q}'.format(p=p, q=q))
    negate = False
    if operator in {'=', '!='}:
        r = inequality(p, q, mem)
        if operator == '=':
            negate = True
        else:
            assert operator == '!='
    elif operator in {'<', '<=', '>=', '>'}:
        swap = False
        if operator == '<=':
            negate = True
            swap = True
        elif operator == '>':
            swap = True
        elif operator == '>=':
            negate = True
        else:
            assert operator == '<'
        if swap:
            p, q = q, p
        r = less_than(p, q, mem)
    else:
        raise ValueError(
            'unknown operator "{op}"'.format(op=operator))
    if negate:
        r = '! {r}'.format(r=r)
    mem.append(r)
    logger.debug('mem = {mem}'.format(mem=_format_mem(mem=mem)))
    logger.debug('-- done flattening "{op}"\n'.format(op=operator))
    return '$ {n} {s}'.format(n=len(mem), s=' '.join(mem))


def inequality(p, q, mem):
    """Return bitvector propositional formula for '!='"""
    assert len(p) == len(q)
    return ' '.join('| ^ {a} {b}'.format(a=a, b=b)
                    for a, b in zip(p, q)) + ' 0'


def less_than(p, q, mem):
    """Return bitvector propositional formula for '<'"""
    res, res_mem, carry = adder_subtractor(
        p, q, add=False, start=len(mem))
    mem.extend(res_mem)
    return '^ ! ^ {a} {b} {carry}'.format(
        a=p[-1], b=q[-1], carry=carry)


def flatten_arithmetic(operator, p, q, mem):
    """Return flattened arithmetic expression."""
    logger.info(
        '++ flatten arithmetic operator "{op}"'.format(op=operator))
    assert isinstance(p, list)
    assert isinstance(q, list)
    assert isinstance(mem, list)
    start = len(mem)
    if operator in {'+', '-'}:
        add = (operator == '+')
        result, res_mem, _ = adder_subtractor(p, q, add, start)
    elif operator == '*':
        res, res_mem = multiplier(p, q, start)
    elif operator == '/':
        res, _, res_mem = restoring_divider(p, q, start)
    elif operator == '%':
        _, res, res_mem = restoring_divider(p, q, start)
    else:
        raise ValueError(
            'Unknown arithmetic operator "{op}"'.format(op=operator))
    mem.extend(res_mem)
    logger.info('-- done flattening "{op}"\n'.format(op=operator))
    return result


def restoring_divider(x, y, start=0):
    """Return divider for bitvectors `x`, `y`.

    @param x: dividend
    @param y: divisor
    @type x, y: `list`
    @param start: memory address to start indexing from
    @type start: `int` >= 0

    @return: (quotient, remainder, memory)
    @rtype: `tuple(list, list, list)`
    """
    # TODO: propagate to propositional context
    # constraint that detects zero divisor
    assert start >= 0, start
    assert isinstance(x, list), x
    assert isinstance(y, list), y
    mem = list()
    j = start
    # rectify
    a, a_mem = abs_(x, j)
    j = _extend_memory(mem, a_mem, j)
    b, b_mem = abs_(y, j)
    j = _extend_memory(mem, b_mem, j)
    # divide
    quo, rem, div_mem = _restoring_divider(a, b, start=j)
    j = _extend_memory(mem, div_mem, j)
    # fix signs
    x_sign = sign(x)
    y_sign = sign(y)
    opposite_signs = '^ {x} {y}'.format(x=x_sign, y=y_sign)
    quo, neg_mem = _negate_if(opposite_signs, quo, start=j)
    j = _extend_memory(mem, neg_mem, j)
    rem, neg_mem = _negate_if(x_sign, rem, start=j)
    j = _extend_memory(mem, neg_mem, j)
    return quo, rem, mem


def _restoring_divider(x, y, s=None, start=0):
    """Return stage `s` of divider (positive).

    @param x: dividend
    @param y: divider
    @type x, y: positive numbers in two's complement
        `list`
    @param s: desired stage of divider
    @type s: `int` with: `-1 <= s <= len(x)`
    @param start: memory address to start indexing from
    @type start: `int` >= 0
    """
    assert start >= 0, start
    assert isinstance(x, list), x
    assert isinstance(y, list), y
    n = len(x)
    # init
    if s is None:
        # double widths
        y = pad(y, 2 * n)
        y = fixed_shift(y, n, left=True)
        s = n - 1
    assert -1 <= s < n, (s, n)
    mem = list()
    j = start
    # base stage: -1
    if s == -1:
        quo = list()
        rem = pad(x, 2 * n)
        return quo, rem, mem
    # stages: 0 ... n - 1
    # recurse
    quo, p, div_mem = _restoring_divider(x, y, s - 1, start=j)
    j = _extend_memory(mem, div_mem, j)
    # this stage
    # diff
    shifted_p = fixed_shift(p, 1, left=True)
    r, sum_mem, carry = adder_subtractor(shifted_p, y, add=False,
                                         start=j, extend_by=0)
    j = _extend_memory(mem, sum_mem, j)
    # quotient
    sgn = sign(r)
    q = '! {sgn}'.format(sgn=sgn)
    quo.insert(0, q)
    # partial remainder
    rem, ite_mem = ite_function(q, r, shifted_p, start=j)
    j = _extend_memory(mem, ite_mem, j)
    # top stage ?
    if s == n - 1:
        rem = rem[n:]
    return quo, rem, mem


def multiplier(x, y, start=0):
    """Return the signed product of `x` and `y`.

    @param x, y: multiplicands
    @type x, y: `list`

    @return: (result, memory)
    @rtype: `tuple(list, list)`
    """
    assert isinstance(x, list), x
    assert isinstance(y, list), y
    nx = len(x)
    ny = len(y)
    n = nx + ny
    p, q = equalize_width(x, y, extend_by=min(nx, ny))
    res, mem = _multiplier(p, q, s=None, start=start)
    assert len(res) == n, (len(res), n)
    if n > ALU_BITWIDTH:
        print('WARNING: (openpromela.bitvector) '
              'Truncating multiplication to {alu} bits.'.format(
                  alu=ALU_BITWIDTH))
        res = truncate(res, ALU_BITWIDTH)
    return res, mem


def _multiplier(x, y, s=None, start=0):
    """Return stage `s` of multiplier.

    @param x, y: multiplicands (in two's complement)
    @param s: desired stage of multiplier
    @type s: `int` with: `-1 <= s < len(y)`
    @param start: memory address to start indexing from
    @type start: `int` >= 0

    @return: (result, memory)
    @rtype: `tuple(list, list)`
    """
    assert start >= 0, start
    assert len(x) == len(y), (x, y)
    n = len(y)
    if s is None:
        s = n - 1
    assert -1 <= s < n, (s, n)
    # base stage: -1
    if s == -1:
        mem = list()
        return ['0'] * len(x), mem
    # stages: 0 ... n - 1
    # recurse
    j = start
    mul_res, mem = _multiplier(x, y, s=s - 1, start=j)
    j += len(mem)
    # this stage
    shifted_x = fixed_shift(x, s, left=True)
    z = ['& {a} {b}'.format(a=a, b=y[s]) for a in shifted_x]
    res, sum_mem, carry = adder_subtractor(
        mul_res, z, add=True, start=j, extend_by=0)
    j = _extend_memory(mem, sum_mem, j)
    assert len(res) == len(x), (x, res, mem)
    return res, mem


def adder_subtractor(x, y, add=True, start=0, extend_by=1):
    """Return sum of `p` and `q`, w/o truncation.

    Implements a ripple-carry adder-subtractor.
    The control signal is `add`.

    Reference
    =========
    https://en.wikipedia.org/wiki/Adder%E2%80%93subtractor
    https://en.wikipedia.org/wiki/Adder_%28electronics%29

    @param x, y: summands (in two's complement)
    @type x, y: `list` of bits
    @param add: if `True` then add, otherwise subtract
    @type add: `bool`
    @param start: insert first element at
        this index in memory structure
    @type start: `int` >= 0
    @param extend_by: extra sign-extension by so many bits
    @type extend_by: `int` >= 0

    @return: (result, memory, carry)
    @type: `tuple(list, list, str)`
    """
    assert start >= 0, start
    assert extend_by >= 0, extend_by
    assert isinstance(x, list), x
    assert isinstance(y, list), y
    dowhat = 'add' if add else 'subtract'
    logger.info('++ {what}...'.format(what=dowhat))
    p, q = equalize_width(x, y, extend_by=extend_by)
    assert len(p) == len(q), (p, q)
    logger.debug('p = {p}\nq = {q}'.format(p=p, q=q))
    # invert
    if add:
        carry = '0'
    else:
        q = ['! {bit}'.format(bit=b) for b in q]
        carry = '1'
    mem = list()
    result = list()
    # use a loop to emphasize the relation
    # between mem, result, carries
    for i, (a, b) in enumerate(zip(p, q)):
        k = start + 2 * i
        r = k + 1
        # full-adder
        # result
        mem.append('^ ^ {a} {b} {c}'.format(a=a, b=b, c=carry))
        result.append('? {k}'.format(k=k))
        # carry
        mem.append(
            '| & {a} {b} & ^ {a} {b} {c}'.format(a=a, b=b, c=carry))
        carry = '? {r}'.format(r=r)
    assert len(mem) == 2 * len(result)
    logger.debug('mem = {mem}\nres = {res}'.format(
        mem=_format_mem(mem), res=result))
    logger.info('-- done {what}ing\n'.format(what=dowhat))
    return result, mem, carry


def barrel_shifter(x, y, s=None, start=0):
    """Return left or right shift formula.

    Recursive implementatin of barrel shifter.
    Note that the shift distance must be represented as unsigned.

    @param x: shift (vector that is to be shifted)
    @type x: `list` of `str`
    @param y: shift distance
    @type y: `list` of `str` with `len(y) == math.log(len(x), 2)`
    @param s: desired stage of barrel shifter
    @type s: `int` with: `-1 <= s < len(y)`
    @param start: memory address to start indexing from
    @type start: `int` >= 0

    @return: 2-tuple:
      1. elements of composition of first `s` stages
      2. memory contents from stage 0 to stage `s`
    @rtype: `tuple([list, list])`
    """
    assert len(y) == math.log(len(x), 2)
    if s is None:
        s = len(y) - 1
    assert -1 <= s < len(y)
    assert start >= 0
    # base stage: -1
    if s == -1:
        mem = list()
        return x, mem
    # stages: 0 ... n - 1
    r, mem = barrel_shifter(x, y, s - 1, start=start)
    for i, a in enumerate(x):
        b = y[s]
        g = r[i]
        h = r[i - 2**s]
        if i < 2**s:
            z = '& ! {b} {g}'.format(b=b, g=g)
        else:
            z = '| & ! {b} {g} & {b} {h}'.format(b=b, g=g, h=h)
        mem.append(z)
    n = len(x)
    m = len(mem) - n
    c = ['? {i}'.format(i=i + m) for i in xrange(n)]
    assert len(c) == len(x)
    return c, mem


def fixed_shift(x, c, left, logical=False, truncate=True):
    """Shift `x` by fixed distance `s`.

    @param x: shift (vector to be shifted)
    @type x: `list` of `str`
    @param c: shift distance
    @type c: `int` with: `0 <= c <= len(x)`
    @param left: if `True` shift left, else right
    @param logical: if `True` insert zeros,
        else replicate sign bit of `x`.
    @param truncate: if `True`, result has same width as `x`

    @return: shifted `x`
    @rtype: `list` of `str`
    """
    n = len(x)
    assert 0 <= c <= n, (c, n, x)
    if left:
        if truncate:
            return c * ['0'] + x[:n - c]
        else:
            return c * ['0'] + x
    # right shift
    # logical or arithmetic ?
    if logical:
        s = '0'
    else:
        s = x[-1]
    return x[c:] + c * [s]


def truncate(x, n):
    """Return first `n` bits of bitvector `x`.

    @type x: `list`
    @type n: `int` >= 0

    @rtype: `list`
    """
    assert n >= 0
    return x[:n]


def ite_function(a, b, c, start):
    """Return memory buffer elements for ite between integers.

    @param a: propositinal formula
    @type a: `str`
    @param b, c: arithmetic formula
    @type b, c: `list`
    @param start: continue indexing buffer cells from this value
    @type start: `int`

    @rtype: `list`
    """
    assert isinstance(a, basestring)
    assert isinstance(b, list)
    assert isinstance(c, list)
    assert len(b) == len(c), (b, c)
    m = list()
    m.append(a)
    for p, q in zip(b, c):
        s = '| & {p} ? {i} & {q} ! ? {i}'.format(p=p, q=q, i=start)
        m.append(s)
    r = ['? {i}'.format(i=i + start + 1) for i, _ in enumerate(b)]
    return r, m


def ite_connective(a, b, c):
    """Return memory buffer for ternary conditional operator.

    Note that economizes by avoiding rewrite formulae.
    In Boolean context, the arguments a, b, c will always
    be variables of type bit, or Boolean constants,
    or the result of expressions as a memory buffer.

    @rtype: `str`
    """
    assert isinstance(a, basestring)
    assert isinstance(b, basestring)
    assert isinstance(c, basestring)
    # local memory buffer
    return '$ 2 {a} | & {b} ? {i} & {c} ! ? {i}'.format(
        a=a, b=b, c=c, i=0)


def var_to_twos_complement(var, t):
    """Return `list` of bits in two's complement."""
    # little-endian encoding
    logger.info(
        '++ encode variable "{var}" to 2s complement'.format(var=var))
    _assert_var_in_table(var, t)
    d = t[var]
    # arithmetic operators defined only for integers
    if d['type'] == 'bool':
        raise TypeError((
            '2s complement undefined for '
            'Boolean variable "{var}"').format(var=var))
    bits = list(d['bitnames'])
    _append_sign_bit(bits, var, d)
    assert len(bits) > 1
    logger.debug('encoded variable "{var}":\n\t{bits}'.format(
        var=var, bits=bits))
    logger.info('-- done encoding variable "{var}".\n'.format(var=var))
    return bits


def _append_sign_bit(bits, var, d):
    """Convert trimmed bitfield to two's complement.

    The bitfield `bits` is modified by appending a sign bit.
    The integer variable represented by `bits` should be sign-definite.
    As given, `bits` is a bitfield that stores the two's complement
    with omitted sign bit, because it is constant.

    @type bits: `list`
    @param d: attributes of integer
    @type d: `dict`
    """
    logger.debug('bits of "{var}": {bits}"'.format(var=var, bits=bits))
    # variable sign ?
    if d['signed']:
        logger.debug('variable "{var}" is signed'.format(var=var))
        if len(bits) < 2:
            raise ValueError(
                'A signed bitvector must have at least 2 bits.\n'
                'Got instead, for variable "{var}",'.format(var=var) +
                ' the bitvector:\n\t {bits}'.format(bits=bits))
        return
    # sign-definite
    logger.debug('variable "{var}" has fixed sign'.format(var=var))
    min_, max_ = d['dom']
    assert min_ * max_ >= 0, (min_, max_)
    # positive ?
    if min_ >= 0:
        sign_bit = '0'
    else:
        sign_bit = '1'
    bits.append(sign_bit)
    assert len(bits) > 1, len(bits)


def _is_bool_var(name, t):
    # fol var ?
    if name in t:
        d = t[name]
        return (d['type'] == 'bool')
    else:
        # bit in a bitvector ?
        int_var = name.rsplit('_', 1)[0]
        is_bit = (
            int_var in t and
            name in t[int_var]['bitnames'])
        if is_bit:
            return True
    _assert_var_in_table(name, t)


def _assert_var_in_table(name, t):
    """Raise `Exception` if variable `name` not in table `t`."""
    # not in variables table ?
    if name in t:
        return
    raise Exception(
        'Variable "{name}" missing from symbol table:\n{t}'.format(
            name=name, t=t))


def int_to_twos_complement(s):
    """Return two's complement of `s` as `list` of `str`.

    @type s: such that `int(s)` is well-defined
    """
    logger.info(
        '++ convert integer "{s}" to 2s complement'.format(s=s))
    x = int(s)
    if x >= 0:
        sign_bit = '0'
        y = x
    else:
        sign_bit = '1'
        n = x.bit_length()
        y = 2**n + x
    # zfill catches the case: y == 0, because lstrip removes 0
    bits = list(reversed(bin(y).lstrip('-0b').zfill(1)))
    bits.append(sign_bit)
    assert x == twos_complement_to_int(bits)
    assert len(bits) > 1
    # bits = sign_extension(bits, n + 1)
    logger.info("two's complement of \"{s}\" is:\n\t{bits}".format(
        s=s, bits=bits))
    logger.info('-- done encoding int\n')
    return bits


def twos_complement_to_int(bits):
    """Return `int` equal to value of two's complement in `bits`."""
    n = len(bits)  # width including sign bit
    n = n - 1  # width w/o sign bit
    r = [int(b) for b in bits]
    return -r[-1] * 2**n + sum(b * 2**i for i, b in enumerate(r[:-1]))


def abs_(x, start=0):
    """Return absolute value of `x`.

    @param start: memory address to start indexing from
    @type start: `int` >= 0
    """
    return _negate_if(sign(x), x, start)


def _negate_if(guard, x, start=0):
    """Return conditional negation of `x`.

    @param guard: if `True`, then negate
    @type guard: `str`
    """
    assert isinstance(x, list), x
    assert start >= 0, start
    n = len(x)
    zero = pad(['0'], len(x))
    j = start
    neg_x, mem, _ = adder_subtractor(
        zero, x, add=False, start=j, extend_by=1)
    ext_x = sign_extension(x, n + 1)
    j += len(mem)
    r, ite_mem = ite_function(guard, neg_x, ext_x, start=j)
    j = _extend_memory(mem, ite_mem, j)
    return r, mem


def equalize_width(x, y, extend_by=0):
    """Return bitvectors of equal len by applying sign extension."""
    logger.info('++ equalize width...')
    logger.debug(
        'before equalization:\n\t x = {x}\n\t y = {y}'.format(
            x=x, y=y))
    n = max(len(x), len(y))
    n += extend_by
    p = sign_extension(x, n)
    q = sign_extension(y, n)
    logger.debug('after extension:\n\t x = {p}\n\t y = {q}'.format(
        p=p, q=q))
    assert len(p) == len(q)
    assert len(p) == n
    logger.info('-- done equalizing.\n')
    return p, q


def sign_extension(x, n):
    """Extend two's complement of `x` to `n` bits width.

    Note that the width of two's complement should be at
    least 2 bits, otherwise it doesn't make sense.

    Reference
    =========
    https://en.wikipedia.org/wiki/Sign_extension

    @type x: `list` of `str`
    @type n: `int` with: `len(x) <= n < 32`
    """
    logger.debug(
        '++ sign extension to {n} bits of: {x}'.format(x=x, n=n))
    assert isinstance(x, list)
    assert n < ALU_BITWIDTH, n
    m = len(x)
    if m < 2:
        raise ValueError('"{x}" has less than 2 bits.'.format(x=x))
    if n < m:
        raise ValueError(
            'Extension width is {n} < {m} = len(x)'.format(n=n, m=m))
    y = x + (n - m) * [x[-1]]
    assert y[:len(x)] == x
    assert len(y) == n
    logger.debug('-- result of extension: {y}\n'.format(y=y))
    return y


def pad(x, n):
    """Return `x` left-padded with zeros to width `n`.

    @type x: `list`
    @type n: `int` > 0
    """
    m = n - len(x)
    assert m > 0, (n, m, x)
    return x + m * ['0']


def sign(x):
    """Return sign bit (MSB) of `x` in two's complement.

    @type x: `list` of `str`
    @return: `str` ('0' or '1')
    """
    return x[-1]


def _extend_memory(mem, more_mem, start):
    """Return new start address after appending memory.

    @param mem: memory to be extended
    @param more_mem: memory elements to append
    @type mem, more_mem: `list`
    @param start: last `mem` element has address `start - 1`
    @type start: `int` with `start >= len(mem)`
    """
    assert start >= len(mem), (start, len(mem))
    mem.extend(more_mem)
    start += len(more_mem)
    return start


def _format_mem(mem):
    """Return pretty string for printing memory contents."""
    return 'memory:\n{mem}\n'.format(
        mem='\n'.join('{i}: {v}'.format(i=i, v=v)
                      for i, v in enumerate(mem)))
