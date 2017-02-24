"""Abstract syntax tree classes for logic."""
# Copyright 2014 by California Institute of Technology
# All rights reserved. Licensed under BSD-3.
#
import astutils


class Nodes(object):
    """Container of AST node classes for logic."""

    Terminal = astutils.Terminal

    class Var(astutils.Terminal):
        """Variable identifier."""

        def __init__(self, value, dtype='var'):
            super(Nodes.Var, self).__init__(value, dtype)

    class Bool(astutils.Terminal):
        """Boolean constant."""

        def __init__(self, value, dtype='bool'):
            super(Nodes.Bool, self).__init__(value, dtype)

    class Num(astutils.Terminal):
        """Numerical costant."""

        def __init__(self, value, dtype='num'):
            super(Nodes.Num, self).__init__(value, dtype)

    class Str(astutils.Terminal):
        """String constant."""

        def __init__(self, value, dtype='str'):
            # the parser removes quotes around `value`
            super(Nodes.Str, self).__init__(value, dtype)

    class Operator(astutils.Operator):
        def flatten(self, *arg, **kw):
            return ''.join([
                self.operator,
                '(',
                ', '.join(
                    x.flatten(*arg, **kw)
                    for x in self.operands),
                ')'])

    class Unary(astutils.Operator):
        """Unary operator."""

    class Binary(astutils.Operator):
        """Binary operator."""

        def flatten(self, *arg, **kw):
            # infix flattener for consistency with parser
            return ' '.join([
                '(',
                self.operands[0].flatten(*arg, **kw),
                self.operator,
                self.operands[1].flatten(*arg, **kw),
                ')'])

    class Comparator(Binary):
        """Binary predicate."""

    class Arithmetic(Binary):
        """Binary function."""
