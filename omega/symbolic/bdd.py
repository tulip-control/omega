"""Slugsin parser with BDD backend.

This module translates Boolean formulas in prefix format
to binary decision diagrams.


Reference
=========

Slugsin syntax:
    https://github.com/VerifiableRobotics/
    slugs/blob/master/doc/input_formats.md
"""
# Copyright 2015 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
from __future__ import absolute_import
import logging
import ply.lex
from omega.logic.ast import Nodes as _Nodes
from omega.logic import syntax as stx


logger = logging.getLogger(__name__)
slugs_log = logging.getLogger(__name__ + '.slugs')


class Lexer(object):
    """Token rules for slugsin lexer."""

    operators = ['NOT', 'AND', 'OR', 'XOR', 'DOLLAR', 'QUESTION',
                 'FORALL', 'EXISTS', 'RENAME', 'DIV']
    identifiers = ['NAME', 'NUMBER']

    t_NUMBER = r'[-]*\d+'
    t_NAME = r"[A-Za-z_][A-Za-z0-9_']*"
    t_FORALL = r'\\A'
    t_EXISTS = r'\\E'
    t_RENAME = r'\\S'
    t_DIV = r'/'
    t_NOT = r'\!'
    t_AND = r'\&'
    t_OR = r'\|'
    t_XOR = r'\^'
    t_DOLLAR = r'\$'
    t_QUESTION = r'\?'
    t_ignore = ' \t'

    def __init__(self):
        self.tokens = self.operators + self.identifiers
        self.build()

    def build(self):
        log = logging.getLogger(__name__ + '.slugs_logger')
        self.lexer = ply.lex.lex(module=self, debug=True, debuglog=log)

    def t_error(self, t):
        raise Exception('Illegal character "{t}"'.format(t=t.value[0]))


class Parser(object):
    """Parser for prefix syntax with buffers."""
    # Context-sensitive grammar, so cannot use PLY

    def __init__(self, nodes=None):
        if nodes is None:
            nodes = Nodes()
        self.nodes = nodes
        self.lexer = Lexer()
        self.tokens = self.lexer.tokens
        self._binary = {'AND', 'OR', 'XOR',
                        'FORALL', 'EXISTS', 'RENAME'}

    def parse(self, data):
        self.lexer.lexer.input(data)
        r = self._recurse()
        # empty stack ?
        tok = self.lexer.lexer.token()
        if not tok:
            return r
        # error
        s = tok.value
        while True:
            tok = self.lexer.lexer.token()
            if not tok:
                break
            s += tok.value
        raise Exception(
            'syntax error: remaining characters: {s}'.format(
                s=s))

    def _recurse(self):
        tok = self.lexer.lexer.token()
        if not tok:
            raise Exception('syntax error: stream ended early')
        t = tok.type
        if t == 'NOT':
            x = self._recurse()
            return self.nodes.Operator('!', x)
        elif t in self._binary:
            op = tok.value
            x = self._recurse()
            y = self._recurse()
            return self.nodes.Operator(op, x, y)
        elif t == 'DOLLAR':
            u = self._recurse()
            assert u.type == 'num', u.type
            n = int(u.value)
            mem = [self._recurse() for i in range(n)]
            return self.nodes.Buffer(mem)
        elif t == 'QUESTION':
            u = self._recurse()
            assert u.type == 'num', u.type
            return self.nodes.Register(u.value)
        elif t == 'NAME':
            return self.nodes.Var(tok.value)
        elif t == 'NUMBER':
            return self.nodes.Num(tok.value)
        else:
            raise Exception('Unknown token "{t}"'.format(t=tok))


class Nodes(_Nodes):
    """AST that evaluates memory buffers."""

    # difference with slugs parser:
    # cyclic references are possible, but assumed absent
    # any cyclic reference would introduce infinite recursion,
    # so a new variable
    class Buffer(object):
        def __init__(self, memory):
            self.memory = memory
            self.type = 'buffer'

        def __repr__(self):
            return 'Memory({c})'.format(
                c=', '.join(repr(u) for u in self.memory))

        def flatten(self, mem=None, same_mem=False, *arg, **kw):
            if not same_mem:
                mem = list()
            for u in self.memory:
                s = u.flatten(mem=mem, *arg, **kw)
                mem.append(s)
            r = mem[-1]
            # print 'mem: ', mem, ', res: ', r
            return r

    class Register(_Nodes.Terminal):
        def __init__(self, value):
            super(Nodes.Register, self).__init__(value)
            self.type = 'register'

        def flatten(self, mem, *arg, **kw):
            i = int(self.value)
            # no circular refs
            assert 0 <= i < len(mem), (i, mem)
            r = mem[i]
            # print 'reg: ', i, ', of mem: ', mem, ', contains: ', r
            return r

    # infix Binary flattening
    class Operator(_Nodes.Operator):
        def flatten(self, *arg, **kw):
            if len(self.operands) == 1:
                return ' '.join([
                    '(',
                    self.operator,
                    self.operands[0].flatten(*arg, **kw),
                    ')'])
            assert len(self.operands) == 2, self.operands
            return ' '.join([
                '(',
                self.operands[0].flatten(*arg, **kw),
                self.operator,
                self.operands[1].flatten(*arg, **kw),
                ')'])


class DebugNodes(Nodes):
    """AST to expand memory buffers."""

    class Buffer(Nodes.Buffer):
        def flatten(self, indent=0, *arg, **kw):
            indent += 1
            sep = ',\n{s}'.format(s=' ' * indent)
            mem = sep.join(
                u.flatten(indent=indent)
                for u in self.memory)
            return '\n{s}buffer[{i}](\n{s1}{mem})'.format(
                i=len(self.memory),
                mem=mem,
                s=' ' * (indent - 1),
                s1=' ' * indent)

    class Register(Nodes.Register):
        def flatten(self, *arg, **kw):
            return 'reg[{i}]'.format(i=self.value)


class BDDNodes(Nodes):
    """AST to flatten prefix syntax to a BDD."""

    class Operator(Nodes.Operator):
        def flatten(self, bdd, mem=None, *arg, **kw):
            # op with variable number of args ?
            if self.operator == '\S':
                pairs, x = self.operands
                operand = x.flatten(bdd=bdd, mem=mem, *arg, **kw)
                mem = list()
                pairs.flatten(bdd=bdd, mem=mem,
                              same_mem=True, *arg, **kw)
                mem = [bdd.support(u).pop() for u in mem]
                rename = {
                    a: b for a, b in zip(mem[1::2], mem[0::2])}
                assert 2 * len(rename) == len(pairs.memory), (
                    rename, pairs.memory)
                r = bdd.rename(operand, rename)
                return r
            operands = [
                u.flatten(bdd=bdd, mem=mem, *arg, **kw)
                for u in self.operands]
            r = bdd.apply(self.operator, *operands)
            # print 'op: ', self.operator, operands, u
            return r

    class Var(Nodes.Var):
        def flatten(self, bdd, *arg, **kw):
            u = bdd.var(self.value)
            # print 'add var: ', self.value, u
            return u

    class Num(Nodes.Num):
        def flatten(self, bdd, *arg, **kw):
            u = int(self.value)
            if u == 0:
                r = bdd.false
            elif u == 1:
                r = bdd.true
            else:
                r = bdd._add_int(u)
            return r


parser = Parser(nodes=BDDNodes())


def add_expr(e, bdd):
    """Add to `bdd` a node for Boolean expression `e`.

    @param e: expression in SLUGSIN syntax
    @type e: `str`
    @param t: symbol table
    @type t: `dict`
    @type bdd: `BDD`

    @return: node in `bdd` corresponding to `e`
    @rtype: `int`
    """
    tree = parser.parse(e)
    u = tree.flatten(bdd=bdd)
    return u


def joint_support(nodes, fol):
    """Return union of supports ."""
    gen = (fol.support(u) for u in nodes)
    return set().union(*gen)


def support_issubset(u, vrs, fol):
    """Return `support(u) <= vrs`.

    Use this function to ensure that only the expected
    variables occur in the expression that a BDD represents.
    This check catches several errors early.

    If `fol` is a `dd.cudd.BDD`, then variable names
    will be bits instead of first-order.

    @param vrs: `set` of variable names as `str`
    """
    support = fol.support(u)
    return support.issubset(vrs)


def is_state_predicate(u):
    """Return `True` if `u` depends only on unprimed values."""
    return not any(stx.isprimed(var) for var in u.support)


def is_primed_state_predicate(u):
    """Return `True` if `u` depends only on primed values."""
    return all(stx.isprimed(var) for var in u.support)


def is_proper_action(u):
    """Return `True` if `u` depends on both primed and unprimed."""
    r = u.support
    return (
        any(stx.isprimed(var) for var in r) and
        any(not stx.isprimed(var) for var in r))


def prime(u, fol):
    """Prime variables in support of state predicate `u`."""
    r = fol.support(u)
    d = {var: stx.prime(var) for var in r}
    return fol.let(d, u)


def unprime(u, fol):
    """Unprime variables in support of `u`.

    Assume only primed variables in support of `u`.
    """
    r = fol.support(u)
    d = {var: stx.unprime(var) for var in r}
    return fol.let(d, u)


def print_support(u, fol):
    """Print separately unprimed and primed vars in support."""
    support = fol.support(u)
    primed_support = set(filter(stx.isprimed, support))
    unprimed_support = support.difference(primed_support)
    print('Unprimed variables in support:')
    print(unprimed_support)
    print('Primed variables in support:')
    print(primed_support)
