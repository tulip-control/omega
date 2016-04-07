"""Slugsin translator to BDDs that uses iteration.

This module translates Boolean formulas in prefix format
to binary decision diagrams.


Reference
=========

Slugsin syntax:
    https://github.com/LTLMoP/slugs/blob/master/doc/input_formats.md
"""
from omega.symbolic.bdd import Lexer


OPERATORS = {'!', '&', '|', '^', '\A', '\E', '\S'}
BINARY_OPERATORS = {'&', '|', '^', '\A', '\E', '\S'}
BINARY = {'AND', 'OR', 'XOR', 'FORALL', 'EXISTS', 'RENAME'}


class Parser(object):
    """Parser for prefix syntax with buffers.

    Avoids recursion by using a stack.
    """
    # Context-sensitive grammar, so cannot use PLY

    def __init__(self):
        self.lexer = Lexer()
        self.tokens = self.lexer.tokens
        self._binary = {'AND', 'OR', 'XOR'}

    def parse(self, data, bdd):
        self.lexer.lexer.input(data)
        mem = None
        r = self._increase(mem, bdd)
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

    def _increase(self, mem, bdd):
        stack = list()
        need = 1
        while need > 0:
            need = self._push(stack, mem, need, bdd)
        return self._reduce(stack, bdd)

    def _push(self, stack, mem, need, bdd):
        tok = self.lexer.lexer.token()
        if not tok:
            raise Exception('syntax error: stream ended early')
        t = tok.type
        if t == 'NAME':
            r = bdd.var(tok.value)
            need -= 1
        elif t == 'NUMBER':
            u = int(tok.value)
            if u == 0:
                r = bdd.false
            elif u == 1:
                r = bdd.true
            else:
                r = bdd._add_int(u)
            need -= 1
        elif t == 'NOT':
            r = tok.value
        elif t in BINARY:
            r = tok.value
            need += 1
        elif t == 'QUESTION':
            tok = self.lexer.lexer.token()
            i = int(tok.value)
            assert 0 <= i < len(mem), (i, mem)
            r = mem[i]
            need -= 1
        elif t == 'DOLLAR':
            tok = self.lexer.lexer.token()
            n = int(tok.value)
            mem = list()
            for i in xrange(n):
                s = self._increase(mem, bdd)
                mem.append(s)
            r = mem[-1]
            need -= 1
        else:
            raise Exception(
                'unknown token type "{t}"'.format(t=t))
        stack.append(r)
        return need

    def _reduce(self, stack, bdd):
        while len(stack) > 1:
            for i, t in enumerate(reversed(stack)):
                if not isinstance(t, basestring):
                    continue
                if t in OPERATORS:
                    break
            assert t in OPERATORS, (
                'unknown operator "{t}"'.format(t=t))
            operator = t
            k = len(stack) - i
            if operator == '!':
                n = 1
            elif t in BINARY_OPERATORS:
                n = 2
            else:
                raise Exception(
                    'unknown operator "{t}"'.format(t=t))
            operands = stack[k:k + n]
            for i in xrange(n):
                stack.pop(k)
            stack.pop(k - 1)
            # print(operator)
            # print(operands)
            u = bdd.apply(operator, *operands)
            stack.insert(k - 1, u)
        (r,) = stack
        return r


parser = Parser()


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
    u = parser.parse(e, bdd)
    return u
