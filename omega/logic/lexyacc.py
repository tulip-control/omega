#!/usr/bin/env python
"""Parser for past and future linear temporal logic.

The syntax is based on that of SPIN.
"""
# the parser is based on that of `tulip`
from __future__ import absolute_import
from omega.logic.ast import Nodes
import astutils


TABMODULE = 'omega.logic.ltl_parsetab'


class Lexer(astutils.Lexer):
    """Token rules to build LTL lexer."""

    reserved = {
        'ite': 'ITE',
        'X': 'NEXT',
        'False': 'FALSE',
        'false': 'FALSE',
        'True': 'TRUE',
        'true': 'TRUE',
        'U': 'UNTIL',
        'W': 'WEAK_UNTIL',
        'V': 'RELEASE',
        'S': 'SINCE',  # as in NuSMV
        'T': 'TRIGGER'}
    values = {'next': 'X'}
    delimiters = ['LPAREN', 'RPAREN', 'DQUOTES', 'COMMA']
    operators = [
        'NOT', 'AND', 'OR', 'XOR', 'IMPLIES', 'EQUIV',
        'EQUALS', 'NEQUALS', 'LT', 'LE', 'GT', 'GE',
        'PLUS', 'MINUS', 'TIMES', 'DIV', 'MOD', 'TRUNCATE',
        'PREVIOUS', 'WEAK_PREVIOUS', 'HISTORICALLY',
        'ALWAYS', 'EVENTUALLY',
        'ONCE', 'PRIME', 'DOT', 'AT',
        'FORALL', 'EXISTS', 'RENAME', 'COLON']
    misc = ['NAME', 'NUMBER']

    def t_NAME(self, t):
        r'[A-Za-z_][A-za-z0-9_]*'
        t.value = self.values.get(t.value, t.value)
        t.type = self.reserved.get(t.value, 'NAME')
        return t

    def t_AND(self, t):
        r'\&\&|\&|/\\'
        t.value = '&'
        return t

    def t_OR(self, t):
        r'\|\||\||\\/'
        t.value = '|'
        return t

    def t_NEQUALS(self, t):
        r'\!\='
        # symbol `#` already marks comments
        return t

    def t_NOT(self, t):
        r'~|\!'
        t.value = '!'
        return t

    def t_IMPLIES(self, t):
        r'\=>|->'
        t.value = '=>'
        return t

    def t_EQUIV(self, t):
        r'\<\=>|\<->'
        t.value = '<->'
        return t

    # quantifiers
    t_FORALL = r'\\A'
    t_EXISTS = r'\\E'
    t_RENAME = r'\\S'  # for arbitrary substitution (compose)
    # conjoin and quantify existentially
    t_COLON = r'\:'
    # Boolean
    t_XOR = r'\^'
    # comparators
    t_EQUALS = r'\='
    t_LT = r'\<'
    t_LE = r'\<\='
    t_GT = r'>\='
    t_GE = r'>'
    # delimiters
    t_LPAREN = r'\('
    t_RPAREN = r'\)'
    t_COMMA = r','
    t_DQUOTES = r'\"'
    # arithmetic
    t_PLUS = r'\+'
    t_MINUS = r'-'
    t_TIMES = r'\*'
    t_DIV = r'/'
    t_MOD = r'\%'
    t_TRUNCATE = r'<<>>'
    # temporal
    t_PREVIOUS = r'--X'
    t_WEAK_PREVIOUS = r'-X'
    t_HISTORICALLY = r'-\[\]'
    t_ONCE = r'-\<\>'
    t_ALWAYS = r'\[\]'
    t_EVENTUALLY = r'\<\>'
    t_DOT = r'\.'
    t_PRIME = r"\'"
    # other
    t_AT = r'@'
    t_NUMBER = r'\d+'
    t_ignore = " \t"

    def t_comment(self, t):
        r'\#.*'
        return

    def t_newline(self, t):
        r'\n+'
        t.lexer.lineno += t.value.count("\n")


class Parser(astutils.Parser):
    """Production rules to build LTL parser."""

    tabmodule = TABMODULE
    start = 'expr'
    # lowest to highest
    # based on precedence in `spin.y`
    precedence = (
        ('left', 'COLON'),
        ('left', 'EQUIV'),
        ('left', 'IMPLIES'),
        ('left', 'XOR'),
        ('left', 'OR'),
        ('left', 'AND'),
        ('left', 'ALWAYS', 'EVENTUALLY', 'HISTORICALLY', 'ONCE'),
        ('left', 'UNTIL', 'WEAK_UNTIL', 'RELEASE', 'SINCE', 'TRIGGER'),
        ('left', 'EQUALS', 'NEQUALS'),
        ('left', 'LT', 'LE', 'GT', 'GE'),
        ('left', 'PLUS', 'MINUS'),
        ('left', 'TIMES', 'DIV', 'MOD'),
        ('right', 'NOT', 'UMINUS'),
        ('left', 'RENAME'),
        ('left', 'FORALL', 'EXISTS'),
        ('right', 'NEXT', 'WEAK_PREVIOUS', 'PREVIOUS'),
        ('left', 'PRIME', 'DOT'))
    Lexer = Lexer
    nodes = Nodes

    def p_nullary(self, p):
        """expr : TRUE
                | FALSE
        """
        p[0] = self.nodes.Bool(p[1])

    def p_postfix_next(self, p):
        """expr : expr PRIME"""
        p[0] = self.nodes.Unary('X', p[1])

    def p_postfix_previous(self, p):
        """expr : expr DOT"""
        p[0] = self.nodes.Unary('-X', p[1])

    def p_postfix_multi_previous(self, p):
        """expr : expr DOT number"""
        p[0] = self.nodes.Unary('-X', p[1], p[2])

    def p_unary(self, p):
        """expr : NOT expr
                | ALWAYS expr
                | EVENTUALLY expr
                | NEXT expr
                | WEAK_PREVIOUS expr
                | PREVIOUS expr
                | HISTORICALLY expr
                | ONCE expr
        """
        p[0] = self.nodes.Unary(p[1], p[2])

    def p_binary_connective(self, p):
        """expr : expr AND expr
                | expr OR expr
                | expr XOR expr
                | expr IMPLIES expr
                | expr EQUIV expr
                | expr UNTIL expr
                | expr WEAK_UNTIL expr
                | expr RELEASE expr
                | expr SINCE expr
                | expr TRIGGER expr
        """
        p[0] = self.nodes.Binary(p[2], p[1], p[3])

    def p_binary_predicate(self, p):
        """expr : expr EQUALS expr
                | expr NEQUALS expr
                | expr LT expr
                | expr LE expr
                | expr GT expr
                | expr GE expr
        """
        p[0] = self.nodes.Comparator(p[2], p[1], p[3])

    def p_binary_function(self, p):
        """expr : expr TIMES expr
                | expr DIV expr
                | expr MOD expr
                | expr PLUS expr
                | expr MINUS expr
        """
        p[0] = self.nodes.Arithmetic(p[2], p[1], p[3])

    def p_truncator(self, p):
        """expr : expr TRUNCATE number"""
        # keep separate to allow overriding
        p[0] = self.nodes.Arithmetic(p[2], p[1], p[3])

    def p_ternary_conditional(self, p):
        """expr : ITE LPAREN expr COMMA expr COMMA expr RPAREN"""
        p[0] = self.nodes.Operator(p[1], p[3], p[5], p[7])

    def p_quantifier(self, p):
        """expr : FORALL list COLON expr
                | EXISTS list COLON expr
        """
        p[0] = self.nodes.Operator(p[1], p[2], p[4])

    def p_substitute(self, p):
        """expr : RENAME pairs COLON expr"""
        p[0] = self.nodes.Operator(p[1], p[2], p[4])

    def p_varlist_iter(self, p):
        """list : list COMMA expr"""
        p[1].append(p[3])
        p[0] = p[1]

    def p_varlist_end(self, p):
        """list : expr"""
        p[0] = [p[1]]

    def p_pairs_iter(self, p):
        """pairs : pairs COMMA pair"""
        p[1].append(p[3])
        p[0] = p[1]

    def p_pairs_end(self, p):
        """pairs : pair"""
        p[0] = [p[1]]

    def p_pair(self, p):
        """pair : expr DIV expr"""
        p[0] = (p[1], p[3])

    def p_paren(self, p):
        """expr : LPAREN expr RPAREN"""
        p[0] = p[2]

    def p_var(self, p):
        """expr : var"""
        p[0] = p[1]

    def p_var_unprimed(self, p):
        """var : NAME"""
        p[0] = self.nodes.Var(p[1])

    def p_bdd_node(self, p):
        """expr : AT number"""
        p[0] = self.nodes.Operator(p[1], p[2])

    def p_number_expr(self, p):
        """expr : number"""
        p[0] = p[1]

    def p_number(self, p):
        """number : NUMBER"""
        p[0] = self.nodes.Num(p[1])

    def p_negative_number(self, p):
        """number : MINUS NUMBER %prec UMINUS"""
        p[0] = self.nodes.Num('-' + p[2])

    def p_string(self, p):
        """expr : DQUOTES NAME DQUOTES"""
        p[0] = self.nodes.Str(p[2])


def _rewrite_tables(outputdir='./'):
    astutils.rewrite_tables(Parser, TABMODULE, outputdir)


if __name__ == '__main__':
    import logging
    log = logging.getLogger('astutils')
    log.setLevel(logging.DEBUG)
    log.addHandler(logging.StreamHandler())
    _rewrite_tables()
