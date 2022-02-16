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
# Copyright 2015 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
import logging
import math

import networkx as nx

from omega.logic import lexyacc
from omega.logic import syntax as stx
from omega.logic.ast import Nodes as _Nodes


ALU_BITWIDTH = 32
DATA_TYPES = {'bool', 'int', 'saturating', 'modwrap'}
KEYS = {'type', 'dom', 'signed', 'width', 'bitnames'}
logger = logging.getLogger(__name__)


def bitblast(f, vrs, defs=None):
    """Flatten formula `f` to bitvector logic.

    @param f:
        quantified first-order action formula
    @type f:
        `str`
    @param vrs:
        symbol table of variables as returned by `bitblast_table`
    @type vrs:
        `dict`
    @param defs:
        operator definitions
    @type defs:
        `dict` that maps
        names (`str`) to
        expressions (`str`)
    """
    if defs is None:
        defs = dict()
    tree = _parser.parse(f)
    defs = {k: _parser.parse(v) for k, v in defs.items()}
    return tree.flatten(t=vrs, defs=defs)


def bitblast_table(table):
    """Return table of variables for bitvectors.

    `table` is a `dict` that maps each variable
    to a `dict` with attributes:

      - "type": `in ('bool', 'saturating', 'modwrap', 'int')`
      - "dom": `tuple([min, max])` where `min, max` are `int`
        used only if "type" is an integer
      - "init" (optional)
    """
    t = dict()
    for var, d in table.items():
        dtype = d['type']
        assert dtype in DATA_TYPES, (var, dtype)
        b = dict(d)  # cp other keys
        for k in KEYS:
            b.pop(k, None)
        if dtype == 'bool':
            b.update(type='bool')
        elif dtype in ('saturating', 'modwrap', 'int'):
            dom = d['dom']
            assert len(dom) == 2, dom
            signed, width = dom_to_width(dom)
            b.update(type='int',
                     signed=signed, width=width,
                     dom=dom)
        else:
            raise Exception(
                f'unknown type: "{dtype}"')
        if dtype == 'int':
            logger.info(
                '"int" found as type '
                '(instead of "saturating")')
        t[var] = b
    _check_data_types(t)
    _add_bitnames(t)
    logger.info('-- done bitblasting vars table\n')
    return t


def type_invariants(table):
    """Return type invariants for variables.

    @param table:
        bitblasted table of integers and Booleans
    @return:
        `(init, safety)`
    @rtype:
        `tuple` of `dict`,
        each `dict` maps variables to `list` of `str`.
    """
    init = dict()
    safety = dict()
    for var, d in table.items():
        init[var] = list()
        safety[var] = list()
        dtype = d['type']
        # initial value
        # imperative var or free var assigned at decl ?
        ival = d.get('init')
        if ival is not None:
            c = _init_to_logic(var, d)
            init[var].append(c)
        # ranged bitfield safety constraints
        if dtype == 'bool':
            continue
        dom = d['dom']
        # int var
        assert dtype in ('int', 'saturating', 'modwrap'), dtype
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
        s = rf'({dmin} <= {var})  /\  ({var} <= {dmax})'
        init[var].append(s)
        # prime needed to enforce limits now, not one step later,
        # otherwise env can violate limits, if that will force
        # sys to lose in the next time step.
        s = (
            rf"    ({dmin} <= {var})  /\  ({var} <= {dmax}) "
            rf" /\ ({dmin} <= {var}') /\  ({var}' <= {dmax})")
        safety[var].append(s)
    return init, safety


def _init_to_logic(var, d):
    """Return logic formulas for initial condition."""
    if d['type'] == 'bool':
        op = '<=>'
    else:
        op = '='
    value = d['init']
    return f'{var} {op} {value}'


def dom_to_width(dom):
    """Return whether integer variable is signed and its bit width.

    @param dom:
        the variable's range
    @type dom:
        `(MIN, MAX)` where `MIN, MAX` are integers
    """
    minval, maxval = dom
    logger.debug(f'int in ({minval}, {maxval})')
    signed = (minval < 0) and (maxval >= 0)
    absval = max(abs(minval), abs(maxval))
    width = absval.bit_length()
    if width == 0:
        assert minval == maxval, (minval, maxval)
        # TODO: optimize by substituting values
        # for variables that are constants
        width = 1
    if signed:
        width = width + 1
    return signed, width


def _add_bitnames(t):
    """Map each integer to a list of bit variables."""
    for var, d in t.items():
        if d['type'] != 'int':
            continue
        assert d['type'] == 'int', d['type']
        if stx.isprimed(var):
            name = stx.unprime(var)
            prime = stx.PRIME
        else:
            name = var
            prime = ''
        bits = [
            f'{name}_{i}{prime}'
            for i in range(d['width'])]
        are_booleans = list(filter(t.__contains__, bits))
        assert not are_booleans, (bits, t)
        d['bitnames'] = bits


def _check_data_types(t):
    types = {'bool', 'int'}
    for var, d in t.items():
        if d['type'] in types:
            continue
        dtype = d['type']
        raise Exception(
            f'unknown type: "{dtype}"')


def bit_table(variables, table):
    """Return symbol table of bits.

    For symbol table definition, see `bitblast_table`.

    @param variables:
        include only these variables
    @type variables:
        `set`
    @param table:
        symbol table of integer and Boolean variables
    @type table:
        `dict` of `dict`
    @return:
        symbol table of bits
    @rtype:
        `dict` of `dict`
    """
    dout = dict()
    keys = {'type', 'dom', 'signed',
            'width', 'bitnames', 'init'}
    for var in variables:
        d = table[var]
        dtype = d['type']
        if dtype == 'int':
            c = d['bitnames']
        elif dtype == 'bool':
            c = [var]
        else:
            raise Exception(
                f'unknown type "{dtype}"')
        dcp = dict(d)  # cp other keys
        for k in keys:
            dcp.pop(k, None)
        for bit in c:
            dbit = dict(dcp)
            dbit.update(type='bool')
            dout[bit] = dbit
    return dout


def list_bits(variables, table):
    """Collect bits of all (integer) `variables`."""
    s = set()
    for x in variables:
        # Boolean ?
        # if table[x]['type'] == 'bool':
        #     s.add(x)
        #     continue
        # integer
        bits = table[x]['bitnames']
        s.update(bits)
    return s


def map_bits_to_integers(table):
    """Return `dict` that maps each bit to an integer or Boolean."""
    bit2int = dict()
    for var, d in table.items():
        dtype = d['type']
        if dtype in ('int', 'saturating', 'modwrap'):
            assert 'bitnames' in d, d
            a = {b: var for b in d['bitnames']}
        elif dtype == 'bool':
            a = {var: var}
        else:
            raise Exception(
                f'unknown var type "{dtype}"')
        bit2int.update(a)
    assert len(bit2int) >= len(table)
    return bit2int


def bitfield_to_int_states(g, t):
    """Convert bitfields to integers for "state" at each node.

    @type g:
        `networkx.DiGraph`
    @type t:
        `VariablesTable`
    @rtype:
        `networkx.Digraph`
    """
    h = nx.DiGraph()
    for u, d in g.nodes(data=True):
        bit_state = d['state']
        int_state = bitfields_to_ints(bit_state, t)
        h.add_node(u, state=int_state)
    for u, v in g.edges():
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

    @param bit_state:
        assignment to all bits
    @type bit_state:
        `dict`
    @type t:
        `VariablesTable`
    """
    int_state = dict()
    for flatname, d in t.items():
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
    """Return symbol table from "simple" `dict`.

    @param env_vars:
        assign `owner` attribute to
        `'env'` if in this set, otherwise to `'sys'`.
    """
    if env_vars is None:
        env_vars = set()
    t = dict()
    for var, dom in d.items():
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


def make_symbol_table(vrs):
    """Return table of declarations from "simple" `dict`."""
    d = dict()
    for var, dom in vrs.items():
        if dom == 'bool':
            d[var] = dict(type='bool')
        else:
            assert len(dom) == 2, dom
            d[var] = dict(type='int', dom=dom)
    return d


def make_dummy_table():
    """Example of a symbol table."""
    t = dict(x=dict(type='bool'),
             y=dict(type='bool'),
             z=dict(type='int', signed=False, width=2),
             w=dict(type='int', signed=False, width=2))
    return t


class Nodes(_Nodes):
    """Return object with AST node classes as attributes."""

    opmap = {
        'false': '0', 'true': '1',
        '~': '!',
        r'\/': '|', '/\\': '&',
        '=>': '| !',
        '=>': '| !',
        '<=>': '! ^',
        'ite': 'ite', '@': '',
        r'\A': r'\A', r'\E': r'\E', r'\S': r'\S',
        'X': '',
        # 'G': '[]', 'F': '<>',
        '<': '<', '<=': '<=', '=<': '<=', '=': '=',
        '>=': '>=', '>': '>', '#': '!=', '/=': '!=', '!=': '!=',
        '+': '+', '-': '-'}

    class Operator(_Nodes.Operator):
        def flatten(self, mem=None, *arg, **kw):
            if self.operator in (r'\A', r'\E'):
                assert mem is None, mem
                x, e = self.operands
                cube = x.flatten(mem=None, *arg, **kw)
                assert isinstance(cube, str), cube
                u = e.flatten(mem=None, *arg, **kw)
                op = Nodes.opmap[self.operator]
                r = f' {op} {cube} {u}'
                return r
            if self.operator == 'params':
                assert mem == None, mem
                # list bits
                # t = kw['t']
                bits = list()
                for v in self.operands:
                    flat = _flatten_var(v, mem=None, **kw)
                    bits.extend(flat)
                cube = (len(bits) - 1) * '& ' + ' '.join(bits)
                return cube
            if self.operator == r'\S':
                x, e = self.operands
                assert isinstance(x, list), x
                unique = set(new.value for new, old in x)
                assert len(unique) == len(x), x  # duplicates ?
                t = kw['t']
                rename = list()
                for new, old in x:
                    # take same values ?
                    old_var = old.value
                    new_var = new.value
                    d_old = t[old_var]
                    d_new = t[new_var]
                    assert d_old['type'] == d_new['type']
                    assert d_old.get('dom') == d_new.get('dom')
                    # flatten
                    a = _flatten_var(old, mem=mem, **kw)
                    b = _flatten_var(new, mem=mem, **kw)
                    assert len(a) == len(b), (a, b)
                    rename.extend(zip(a, b))
                pairs = ' '.join(
                    f'{b} {a}'
                    for a, b in rename)
                u = e.flatten(mem=mem, **kw)
                n = 2 * len(rename)
                op = Nodes.opmap[self.operator]
                r = f' {op} ${n} {pairs} {u}'
                return r
            if self.operator == 'LET':
                # populate local scope
                global_defs = kw.get('defs', dict())
                defs = dict(global_defs)  # isolate context
                local_defs, e = self.operands
                kw = dict(kw)  # local scope instead
                kw.pop('defs')
                for op_def in local_defs:
                    op_def.flatten(defs=defs, mem=mem, *arg, **kw)
                # flatten expr in local scope
                r = e.flatten(defs=defs, mem=mem, *arg, **kw)
                return r
            if self.operator == '@':
                # priming of state predicate BDDs unsupported yet
                assert not kw.get('prime'), kw
                x = int(self.operands[0].value)
                assert x != 0, x
                return '@' + str(x)
            if self.operator == '/\\':
                ops = [
                    u.flatten(mem=mem, *arg, **kw)
                    for u in self.operands]
                return stx.conj_prefix(ops)
            if self.operator == r'\/':
                ops = [
                    u.flatten(mem=mem, *arg, **kw)
                    for u in self.operands]
                return stx.disj_prefix(ops)
            if self.operator != 'ite':
                return super().flatten(
                    mem=mem, *arg, **kw)
            # ternary conditional
            assert self.operator == 'ite', self.operator
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
            logger.info(f'flatten "{repr(self)}"')
            if self.operator == 'X' or self.operator == "'":
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
            logger.info(f'flatten "{repr(self)}"')
            op = self.operator
            x, y = self.operands
            if op == '==':
                name = x.value
                defs = kw['defs']  # must be in some context
                assert name not in defs, (
                    f'attempted redefining "{name}"')
                defs[name] = y
                return
            x = x.flatten(*arg, **kw)
            y = y.flatten(*arg, **kw)
            if op == '..':
                return (x, y)
            elif op == r'\in':
                assert len(y) == 2, y
                e = x
                a, b = y
                x = flatten_comparator('<=', a, e, mem=list())
                y = flatten_comparator('<=', e, b, mem=list())
                op = '/\\'
            op = Nodes.opmap[op]
            assert isinstance(x, str), x
            assert isinstance(y, str), y
            return f' {op} {x} {y} '

    class Var(_Nodes.Var):
        def flatten(self, prime=None, mem=None,
                    t=None, defs=None, *arg, **kw):
            logger.info(f'flatten "{repr(self)}"')
            name = self.value
            # operator definition ?
            if defs is not None and name in defs:
                u = defs[name]
                # BDD ?
                if hasattr(u, 'var'):
                    return str(u)
                # list at arithmetic level ?
                if isinstance(u, list):
                    return u
                # not ast ?
                if not hasattr(u, 'flatten'):
                    return u
                # ast
                return u.flatten(
                    prime=prime, mem=mem, t=t, defs=defs,
                    *arg, **kw)
            if _is_bool_var(name, t):
                # Boolean scope ?
                # This check was relevant when
                # Boolean-valued variables could
                # appear only in Boolean scope.
                #
                # Boolean-valued variables can
                # appear in arithmetic scope
                # under the equality operator `=`.
                # if name in t:
                #     assert mem is None, mem
                prime = stx.PRIME if prime else ''
                return f'{name}{prime}'
            assert name in t, (
                f'"{name}" neither var nor operator')
            # arithmetic context
            # must be integer variable
            # a refinement occurs here automatically
            bits = var_to_twos_complement(name, t)
            def make_bit(b):
                if prime and not b[0].isdigit():
                    suffix = stx.PRIME
                else:
                    suffix = ''
                return f'{b}{suffix}'
            bits = [make_bit(b) for b in bits]
            return bits

    class Num(_Nodes.Num):
        def flatten(self, *arg, **kw):
            logger.info(f'flatten "{repr(self)}"')
            return int_to_twos_complement(self.value)

    class Bool(_Nodes.Bool):
        def flatten(self, *arg, **kw):
            return Nodes.opmap[self.value.lower()]

    class Comparator(_Nodes.Comparator):
        def flatten(self, mem=None, *arg, **kw):
            logger.info(f'flatten "{repr(self)}"')
            assert mem is None, (
                f'"{self}" appears in arithmetic scope')
            mem = list()
            p = self.operands[0].flatten(mem=mem, *arg, **kw)
            q = self.operands[1].flatten(mem=mem, *arg, **kw)
            # arithmetic or Boolean operands ?
            if isinstance(p, list) and isinstance(q, list):
                return flatten_comparator(self.operator, p, q, mem)
            else:
                op = self.operator
                assert op in ('=', '#', '/=', '!='), op
                if op == '=':
                    pref = '! ^'
                else:
                    pref = '^'
                return f'{pref} {p} {q}'

    class Arithmetic(_Nodes.Arithmetic):
        def flatten(self, mem=None, *arg, **kw):
            if self.operator == '<<>>':
                return flatten_truncator(
                    self.operands, mem=mem, *arg, **kw)
            logger.info(f'flatten "{repr(self)}"')
            # only for testing purposes
            assert mem is not None, (
                f'Arithmetic formula "{self}" '
                'in Boolean scope.')
            p = self.operands[0].flatten(mem=mem, *arg, **kw)
            q = self.operands[1].flatten(mem=mem, *arg, **kw)
            return flatten_arithmetic(self.operator, p, q, mem)


_parser = lexyacc.Parser(nodes=Nodes())


def flatten_truncator(operands, mem=None, *arg, **kw):
    """Return integer truncated to given width."""
    logger.info(
        f'++ flatten truncator "{operands}"')
    p = operands[0].flatten(mem=mem, *arg, **kw)
    assert isinstance(p, list), p
    y = operands[1]
    assert isinstance(y, Nodes.Num), (type(y), y)
    n = int(y.value)
    tr = truncate(p, n)
    # if extended, should not use MSB of truncation
    tr.append('0')
    logger.debug(f'truncation result: {tr}\n')
    logger.info('-- done flattening truncator.\n')
    return tr


def flatten_comparator(operator, x, y, mem):
    """Return flattened comparator formula."""
    logger.info(
        f'++ flatten comparator "{operator}" ...')
    assert isinstance(x, list), x
    assert isinstance(y, list), y
    p, q = equalize_width(x, y)
    assert len(p) == len(q), (p, q)
    logger.debug(f'p = {p}\nq = {q}')
    negate = False
    if operator in {'=', '#', '/=', '!='}:
        r = inequality(p, q, mem)
        if operator == '=':
            negate = True
        else:
            assert (operator == '#'
                or operator == '/='
                or operator == '!='), operator
    elif operator in {'<', '<=', '=<', '>=', '>'}:
        swap = False
        if operator == '<=':
            negate = True
            swap = True
        elif operator == '>':
            swap = True
        elif operator == '>=' or operator == '=<':
            negate = True
        else:
            assert operator == '<', operator
        if swap:
            p, q = q, p
        r = less_than(p, q, mem)
    else:
        raise ValueError(
            f'unknown operator "{operator}"')
    if negate:
        r = f'! {r}'
    mem.append(r)
    logger.debug(f'mem = {_format_mem(mem=mem)}')
    logger.debug(f'-- done flattening "{operator}"\n')
    s = ' '.join(mem)
    return f'$ {len(mem)} {s}'


def inequality(p, q, mem):
    """Return bitvector propositional formula for '#'."""
    assert len(p) == len(q), (p, q)
    return ' '.join(f'| ^ {a} {b}'
                    for a, b in zip(p, q)) + ' 0'


def less_than(p, q, mem):
    """Return bitvector propositional formula for '<'."""
    res, res_mem, carry = adder_subtractor(
        p, q, add=False, start=len(mem))
    mem.extend(res_mem)
    return f'^ ! ^ {p[-1]} {q[-1]} {carry}'


def flatten_arithmetic(operator, p, q, mem):
    """Return flattened arithmetic expression."""
    logger.info(
        f'++ flatten arithmetic operator "{operator}"')
    assert isinstance(p, list), p
    assert isinstance(q, list), q
    assert isinstance(mem, list), mem
    start = len(mem)
    if operator in {'+', '-'}:
        add = (operator == '+')
        result, res_mem, _ = adder_subtractor(p, q, add, start)
    elif operator == '*':
        result, res_mem = multiplier(p, q, start)
    elif operator == '/':
        result, _, res_mem = restoring_divider(p, q, start)
    elif operator == '%':
        _, result, res_mem = restoring_divider(p, q, start)
    else:
        raise ValueError(
            f'Unknown arithmetic operator "{operator}"')
    mem.extend(res_mem)
    logger.info(f'-- done flattening "{operator}"\n')
    return result


def restoring_divider(x, y, start=0):
    """Return divider for bitvectors `x`, `y`.

    @param x:
        dividend
    @param y:
        divisor
    @type x, y:
        `list`
    @param start:
        memory address to start indexing from
    @type start:
        `int` >= 0
    @return:
        (quotient, remainder, memory)
    @rtype:
        `tuple(list, list, list)`
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
    opposite_signs = f'^ {x_sign} {y_sign}'
    quo, neg_mem = _negate_if(opposite_signs, quo, start=j)
    j = _extend_memory(mem, neg_mem, j)
    rem, neg_mem = _negate_if(x_sign, rem, start=j)
    j = _extend_memory(mem, neg_mem, j)
    return quo, rem, mem


def _restoring_divider(x, y, s=None, start=0):
    """Return stage `s` of divider (positive).

    @param x:
        dividend
    @param y:
        divider
    @type x, y:
        positive numbers in two's complement
        `list`
    @param s:
        desired stage of divider
    @type s:
        `int` with:
        `-1 <= s <= len(x)`
    @param start:
        memory address to start indexing from
    @type start:
        `int` >= 0
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
    r, sum_mem, carry = adder_subtractor(
        shifted_p, y,
        add=False, start=j, extend_by=0)
    j = _extend_memory(mem, sum_mem, j)
    # quotient
    sgn = sign(r)
    q = f'! {sgn}'
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

    @param x, y:
        multiplicands
    @type x, y:
        `list`
    @return:
        (result, memory)
    @rtype:
        `tuple(list, list)`
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
        print('WARNING: (bitvector) '
              f'Truncating multiplication to {ALU_BITWIDTH} bits.')
        res = truncate(res, ALU_BITWIDTH)
    return res, mem


def _multiplier(x, y, s=None, start=0):
    """Return stage `s` of multiplier.

    @param x, y:
        multiplicands (in two's complement)
    @param s:
        desired stage of multiplier
    @type s:
        `int` with:
        `-1 <= s < len(y)`
    @param start:
        memory address to start indexing from
    @type start:
        `int` >= 0
    @return:
        (result, memory)
    @rtype:
        `tuple(list, list)`
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
    b = y[s]
    z = [f'& {a} {b}' for a in shifted_x]
    res, sum_mem, carry = adder_subtractor(
        mul_res, z, add=True, start=j, extend_by=0)
    j = _extend_memory(mem, sum_mem, j)
    assert len(res) == len(x), (x, res, mem)
    return res, mem


def adder_subtractor(x, y, add=True, start=0, extend_by=1):
    """Return sum of `p` and `q`, without truncation.

    Implements a ripple-carry adder-subtractor.
    The control signal is `add`.

    Reference
    =========
    <https://en.wikipedia.org/wiki/Adder%E2%80%93subtractor>
    <https://en.wikipedia.org/wiki/Adder_%28electronics%29>

    @param x, y:
        summands (in two's complement)
    @type x, y:
        `list` of bits
    @param add:
        if `True` then add, otherwise subtract
    @type add:
        `bool`
    @param start:
        insert first element at
        this index in memory structure
    @type start:
        `int` >= 0
    @param extend_by:
        extra sign-extension by so many bits
    @type extend_by:
        `int` >= 0
    @return:
        (result, memory, carry)
    @type:
        `tuple(list, list, str)`
    """
    assert start >= 0, start
    assert extend_by >= 0, extend_by
    assert isinstance(x, list), x
    assert isinstance(y, list), y
    dowhat = 'add' if add else 'subtract'
    logger.info(f'++ {dowhat}...')
    p, q = equalize_width(x, y, extend_by=extend_by)
    assert len(p) == len(q), (p, q)
    logger.debug(f'p = {p}\nq = {q}')
    # invert
    if add:
        carry = '0'
    else:
        q = [f'! {bit}' for bit in q]
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
        mem.append(f'^ ^ {a} {b} {carry}')
        result.append(f'? {k}')
        # carry
        mem.append(
            f'| & {a} {b} & ^ {a} {b} {carry}')
        carry = f'? {r}'
    assert len(mem) == 2 * len(result), (mem, result)
    logger.debug(
        f'mem = {_format_mem(mem)}\n'
        f'res = {result}')
    logger.info(f'-- done {dowhat}ing\n')
    return result, mem, carry


def barrel_shifter(x, y, s=None, start=0):
    """Return left or right shift formula.

    Recursive implementatin of barrel shifter.
    Note that the shift distance must be represented as unsigned.

    @param x:
        shift (vector that is to be shifted)
    @type x:
        `list` of `str`
    @param y:
        shift distance
    @type y:
        `list` of `str` with
        `len(y) == math.log(len(x), 2)`
    @param s:
        desired stage of barrel shifter
    @type s:
        `int` with:
        `-1 <= s < len(y)`
    @param start:
        memory address to start indexing from
    @type start:
        `int` >= 0
    @return:
        2-tuple:
        1. elements of composition of first `s` stages
        2. memory contents from stage 0 to stage `s`
    @rtype:
        `tuple([list, list])`
    """
    assert len(y) == math.log(len(x), 2), (x, y)
    if s is None:
        s = len(y) - 1
    assert -1 <= s < len(y), (s, y)
    assert start >= 0, start
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
            z = f'& ! {b} {g}'
        else:
            z = f'| & ! {b} {g} & {b} {h}'
        mem.append(z)
    n = len(x)
    m = len(mem) - n
    c = [f'? {i + m}' for i in range(n)]
    assert len(c) == len(x), (c, x)
    return c, mem


def fixed_shift(x, c, left, logical=False, truncate=True):
    """Shift `x` by fixed distance `s`.

    @param x:
        shift (vector to be shifted)
    @type x:
        `list` of `str`
    @param c:
        shift distance
    @type c:
        `int` with:
        `0 <= c <= len(x)`
    @param left:
        if `True` shift left,
        else right
    @param logical:
        if `True` insert zeros,
        else replicate sign bit of `x`.
    @param truncate:
        if `True`, result has same width as `x`
    @return:
        shifted `x`
    @rtype:
        `list` of `str`
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

    @type x:
        `list`
    @type n:
        `int` >= 0
    @rtype:
        `list`
    """
    assert n >= 0, n
    return x[:n]


def ite_function(a, b, c, start):
    """Return memory buffer elements for ite between integers.

    @param a:
        propositinal formula
    @type a:
        `str`
    @param b, c:
        arithmetic formula
    @type b, c:
        `list`
    @param start:
        continue indexing buffer cells from this value
    @type start:
        `int`
    @rtype:
        `list`
    """
    assert isinstance(a, str), a
    assert isinstance(b, list), b
    assert isinstance(c, list), c
    assert len(b) == len(c), (b, c)
    m = list()
    m.append(a)
    for p, q in zip(b, c):
        s = f'| & {p} ? {start} & {q} ! ? {start}'
        m.append(s)
    r = [f'? {i + start + 1}' for i, _ in enumerate(b)]
    return r, m


def ite_connective(a, b, c):
    """Return memory buffer for ternary conditional operator.

    Note that economizes by avoiding rewrite formulas.
    In Boolean context, the arguments a, b, c will always
    be variables of type bit, or Boolean constants,
    or the result of expressions as a memory buffer.

    @rtype:
        `str`
    """
    assert isinstance(a, str), a
    assert isinstance(b, str), b
    assert isinstance(c, str), c
    # local memory buffer
    i = 0
    return f'$ 2 {a} | & {b} ? {i} & {c} ! ? {i}'


def var_to_twos_complement(var, t):
    """Return `list` of bits in two's complement."""
    # little-endian encoding
    logger.info(
        f'++ encode variable "{var}" to 2s complement')
    _assert_var_in_table(var, t)
    d = t[var]
    # arithmetic operators defined only for integers
    if d['type'] == 'bool':
        raise TypeError(
            '2s complement undefined for '
            f'Boolean variable "{var}"')
    bits = list(d['bitnames'])
    _append_sign_bit(bits, var, d)
    assert len(bits) > 1, bits
    logger.debug(f'encoded variable "{var}":\n\t{bits}')
    logger.info(f'-- done encoding variable "{var}".\n')
    return bits


def _append_sign_bit(bits, var, d):
    """Convert trimmed bitfield to two's complement.

    The bitfield `bits` is modified by appending a sign bit.
    The integer variable represented by
    `bits` should be sign-definite.
    As given, `bits` is a bitfield that
    stores the two's complement
    with omitted sign bit, because it is constant.

    @type bits:
        `list`
    @param d:
        attributes of integer
    @type d:
        `dict`
    """
    logger.debug(f'bits of "{var}": {bits}"')
    # variable sign ?
    if d['signed']:
        logger.debug(f'variable "{var}" is signed')
        if len(bits) < 2:
            raise ValueError(
                'A signed bitvector must have at least 2 bits.\n'
                f'Got instead, for variable "{var}",'
                f' the bitvector:\n\t {bits}')
        return
    # sign-definite
    logger.debug(f'variable "{var}" has fixed sign')
    min_, max_ = d['dom']
    assert min_ * max_ >= 0, (min_, max_)
    # positive ?
    if min_ >= 0:
        sign_bit = '0'
    else:
        assert max_ < 0, max_  # only negative values
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
        if int_var in t and 'bitnames' not in t[int_var]:
            raise ValueError(int_var, t)
        is_bit = (
            int_var in t and
            name in t[int_var]['bitnames'])
        return is_bit


def _assert_var_in_table(name, t):
    """Raise `Exception` if variable `name` not in table `t`."""
    # not in variables table ?
    if name in t:
        return
    raise Exception(
        f'Variable "{name}" missing from symbol table:\n{t}')


def int_to_twos_complement(s):
    """Return two's complement of `s` as `list` of `str`.

    @type s:
        such that `int(s)` be well-defined
    """
    logger.info(
        f'++ convert integer "{s}" to 2s complement')
    x = int(s)
    n = x.bit_length()
    if x >= 0:
        sign_bit = '0'
        y = x
    else:
        sign_bit = '1'
        y = 2**n + x
    m = max(n, 1)  # if y == 0 then n == 0
    bits = bin(y).lstrip('-0b').zfill(m)
    bits = list(reversed(bits))
    bits.append(sign_bit)
    x_ = twos_complement_to_int(bits)
    assert x == x_, (x, x_)
    assert len(bits) > 1, bits
    # bits = sign_extension(bits, n + 1)
    logger.info(f"two's complement of \"{s}\" is:\n\t{bits}")
    logger.info('-- done encoding int\n')
    return bits


def twos_complement_to_int(bits):
    """Return `int` equal to value of two's complement in `bits`."""
    n = len(bits)  # width including sign bit
    n = n - 1  # width without sign bit
    r = [int(b) for b in bits]
    return -r[-1] * 2**n + sum(
        b * 2**i
        for i, b in enumerate(r[:-1]))


def abs_(x, start=0):
    """Return absolute value of `x`.

    @param start:
        memory address to start indexing from
    @type start:
        `int` >= 0
    """
    return _negate_if(sign(x), x, start)


def _negate_if(guard, x, start=0):
    """Return conditional negation of `x`.

    @param guard:
        if `True`, then negate
    @type guard:
        `str`
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
        f'before equalization:\n\t x = {x}\n\t y = {y}')
    n = max(len(x), len(y))
    n += extend_by
    p = sign_extension(x, n)
    q = sign_extension(y, n)
    logger.debug(f'after extension:\n\t x = {p}\n\t y = {q}')
    assert len(p) == len(q), (p, q)
    assert len(p) == n, (p, n)
    logger.info('-- done equalizing.\n')
    return p, q


def sign_extension(x, n):
    """Extend two's complement of `x` to `n` bits width.

    Note that the width of two's complement should be at
    least 2 bits, otherwise it doesn't make sense.

    Reference
    =========
    <https://en.wikipedia.org/wiki/Sign_extension>

    @type x:
        `list` of `str`
    @type n:
        `int` with:
        `len(x) <= n < 32`
    """
    logger.debug(
        f'++ sign extension to {n} bits of: {x}')
    assert isinstance(x, list), x
    assert n < ALU_BITWIDTH, n
    m = len(x)
    if m < 2:
        raise ValueError(f'"{x}" has less than 2 bits.')
    if n < m:
        raise ValueError(
            f'Extension width is {n} < {m} = len(x)')
    y = x + (n - m) * [x[-1]]
    assert y[:len(x)] == x, (y, x)
    assert len(y) == n, (y, n)
    logger.debug(f'-- result of extension: {y}\n')
    return y


def pad(x, n):
    """Return `x` left-padded with zeros to width `n`.

    @type x:
        `list`
    @type n:
        `int` > 0
    """
    m = n - len(x)
    assert m > 0, (n, m, x)
    return x + m * ['0']


def sign(x):
    """Return sign bit (MSB) of `x` in two's complement.

    @type x:
        `list` of `str`
    @return:
        `str` ('0' or '1')
    """
    return x[-1]


def _extend_memory(mem, more_mem, start):
    """Return new start address after appending memory.

    @param mem:
        memory to be extended
    @param more_mem:
        memory elements to append
    @type mem, more_mem:
        `list`
    @param start:
        last `mem` element has address `start - 1`
    @type start:
        `int` with
        `start >= len(mem)`
    """
    assert start >= len(mem), (start, len(mem))
    mem.extend(more_mem)
    start += len(more_mem)
    return start


def _format_mem(mem):
    """Return pretty string for printing memory contents."""
    return 'memory:\n{mem}\n'.format(
        mem='\n'.join(f'{i}: {v}'
                      for i, v in enumerate(mem)))


def _flatten_var(v, *arg, **kw):
    """Return `list` of bits, for both integer and Boolean var."""
    flat = v.flatten(*arg, **kw)
    # bool ?
    if stx.isinstance_str(flat):
        flat = [flat]
    bits = _filter_trailing_zeros(flat)
    return bits


def _filter_trailing_zeros(flat):
    return [b for b in flat if not b[0].isdigit()]
