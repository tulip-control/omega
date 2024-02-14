"""Slugsin parser with BDD backend.

This module translates Boolean formulas in prefix format
to binary decision diagrams.


Reference
=========

Slugsin syntax:
    <https://github.com/VerifiableRobotics/
    slugs/blob/master/doc/input_formats.md>
"""
# Copyright 2015 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
import logging

import ply.lex

from omega.logic.ast import Nodes as _Nodes


logger = logging.getLogger(__name__)
slugs_log = logging.getLogger(__name__ + '.slugs')


class Lexer:
    """Token rules for slugsin lexer."""

    t_AT = r' @ '
    t_NUMBER = r' [-]* \d+ '
    t_NAME = r'''
        [A-Za-z_]
        [A-Za-z0-9_']*
        '''
    t_FORALL = r' \\A '
    t_EXISTS = r' \\E '
    t_RENAME = r' \\S '
    t_DIV = r' / '
    t_NOT = r' ! '
    t_AND = r' \& '
    t_OR = r' \| '
    t_XOR = r' \^ '
    t_DOLLAR = r' \$ '
    t_QUESTION = r' \? '
    t_ignore = ''.join(['\x20', '\t'])

    def __init__(self):
        self.operators = [
            'NOT', 'AND', 'OR', 'XOR',
            'DOLLAR', 'QUESTION',
            'FORALL', 'EXISTS',
            'RENAME', 'DIV', 'AT']
        self.identifiers = ['NAME', 'NUMBER']
        self.tokens = self.operators + self.identifiers
        self.build()

    def build(self):
        log = logging.getLogger(__name__ + '.slugs_logger')
        self.lexer = ply.lex.lex(module=self, debug=True, debuglog=log)

    def t_error(self, t):
        raise Exception(f'Illegal character "{t.value[0]}"')


class Parser:
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
            f'syntax error: remaining characters: {s}')

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
        elif t == 'AT':
            return self._recurse()
        elif t == 'NUMBER':
            return self.nodes.Num(tok.value)
        else:
            raise Exception(f'Unknown token "{tok}"')


class Nodes(_Nodes):
    """AST that evaluates memory buffers."""

    # difference with slugs parser:
    # cyclic references are possible, but assumed absent
    # any cyclic reference would introduce infinite recursion,
    # so a new variable
    class Buffer:
        def __init__(self, memory):
            self.memory = memory
            self.type = 'buffer'

        def __repr__(self):
            c = ', '.join(repr(u) for u in self.memory)
            return f'Memory({c})'

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
            super().__init__(value)
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
            blank = ' ' * indent
            sep = f',\n{blank}'
            mem = sep.join(
                u.flatten(indent=indent)
                for u in self.memory)
            i = len(self.memory)
            s = ' ' * (indent - 1)
            s1 = ' ' * indent
            return f'\n{s}buffer[{i}](\n{s1}{mem})'


    class Register(Nodes.Register):
        def flatten(self, *arg, **kw):
            return f'reg[{self.value}]'


class BDDNodes(Nodes):
    """AST to flatten prefix syntax to a BDD."""

    class Operator(Nodes.Operator):
        def flatten(self, bdd, mem=None, *arg, **kw):
            # op with variable number of args ?
            if self.operator == r'\S':
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

    @param e:
        expression in SLUGSIN syntax
    @type e:
        `str`
    @param t:
        symbol table
    @type t:
        `dict`
    @type bdd:
        `BDD`
    @return:
        node in `bdd` corresponding to `e`
    @rtype:
        `int`
    """
    tree = parser.parse(e)
    u = tree.flatten(bdd=bdd)
    return u
