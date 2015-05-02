"""Utilities for creating formulae."""


def conj(iterable, sep=''):
    return _associative_op(iterable, '&', sep)


def disj(iterable, sep=''):
    return _associative_op(iterable, '|', sep)


def _associative_op(iterable, op, sep):
    """Apply associative binary operator `op`, using `sep` as separator."""
    if op not in {'&', '|'}:
        raise Exception('operator "{op}" not supported.'.format(op=op))
    true = 'True'
    false = 'False'
    if op == '&':
        true, false = false, true
    glue = ') ' + sep + op + ' ('
    # avoid consuming a generator
    h = [x for x in iterable if x]
    return _recurse_op(0, len(h), h, true, false, glue)


def _recurse_op(a, b, h, true, false, glue):
    """Apply binary operator recursively.

    @param a: start of sublist
    @type a: int in [0, len(h)]
    @param b: end of sublist
    @type b: int in [0, len(h)]
    @param h: `list`
    @param true, false: permutation of 'True', 'False'
    @param glue: used to concatenate a, b
    """
    n = b - a
    # empty ?
    if not n:
        return false
    # singleton ?
    if n == 1:
        return h[a]
    # power of 2 ?
    m = (n - 1).bit_length() - 1
    c = a + 2**m
    x = _recurse_op(a, c, h, true, false, glue)
    y = _recurse_op(c, b, h, true, false, glue)
    # controlling value ?
    # don't care ?
    if x == true or y == true:
        return true
    if x == false:
        return y
    if y == false:
        return x
    return '(' + x + glue + y + ')'


def paren(iterable):
    return ('(' + x + ')' for x in iterable)


def linear_disj(s, op='||'):
    b = ' {op} '.format(op=op)
    return b.join('({x})'.format(x=x) for x in s if x != '')


def linear_conj(s, op='&&'):
    b = ' {op} '.format(op=op)
    return b.join('({x})'.format(x=x) for x in s if x != '')


def conj_intersection(s, r, paren=True):
    if paren:
        return ' && '.join('({x})'.format(x=x) for x in s if x in r)
    else:
        return ' && '.join('{x}'.format(x=x) for x in s if x in r)


def conj_neg(s, paren=True):
    if paren:
        return ' && '.join('!({x})'.format(x=x) for x in s)
    else:
        return ' && '.join('!{x}'.format(x=x) for x in s)
