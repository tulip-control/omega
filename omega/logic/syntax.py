"""Utilities for creating formulae."""
import logging
import math


logger = logging.getLogger(__name__)
PRIME = "'"
SUPPORTED_OPERATORS = {'&', '|', '/\\', '\/'}


def conj(iterable, sep='', op='&'):
    """Return binary conjunction in infix syntax."""
    return _associative_op(iterable, op, sep)


def disj(iterable, sep='', op='|'):
    """Return binary disjunction in prefix syntax."""
    return _associative_op(iterable, op, sep)


def _associative_op(iterable, op, sep):
    """Apply associative binary operator `op`.

    @param sep: separator
    """
    if op not in SUPPORTED_OPERATORS:
        raise Exception(
            'operator "{op}" not supported.'.format(op=op))
    true = 'True'
    false = 'False'
    if op in ('&', '/\\'):
        true, false = false, true
    glue = (') ' + sep + op + ' (')
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
    assert n > 1, n
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
    """Return generator that parenthesizes elements."""
    return ('(' + x + ')' for x in iterable)


def linear_disj(s, op='||'):
    """Return linear disjunction in prefix syntax."""
    b = ' {op} '.format(op=op)
    return b.join('({x})'.format(x=x) for x in s if x != '')


def linear_conj(s, op='&&'):
    """Return linear conjunction in prefix syntax."""
    b = ' {op} '.format(op=op)
    return b.join('({x})'.format(x=x) for x in s if x != '')


def disj_prefix(iterable, op='|', false='0', true='1'):
    """Return linear disjunction in prefix syntax."""
    return _prefix_linear(iterable, op, false, true)


def conj_prefix(iterable, op='&', false='0', true='1'):
    """Return linear conjunction in prefix syntax."""
    false, true = true, false
    return _prefix_linear(iterable, op, false, true)


# TODO: recursive version
def _prefix_linear(s, op, false, true):
    """Apply associative binary operator linearly.

    @param s: container
    @param op: operator
    @param false, true: values if treating `op` as disjunction
    """
    if not s:
        return false
    u = s[0]
    for v in s[1:]:
        # controlling value ?
        if u == true:
            break
        if v == true:
            u = true
            break
        u = op + ' ' + u + ' ' + v
    return u


def conj_intersection(s, r, paren=True):
    if paren:
        return conj(
            '({x})'.format(x=x) for x in s if x in r)
    else:
        return conj(
            '{x}'.format(x=x) for x in s if x in r)


def conj_neg(s, paren=True):
    if paren:
        return conj('!({x})'.format(x=x) for x in s)
    else:
        return conj('!{x}'.format(x=x) for x in s)


def recurse_binary_log_space(f, x, n):
    """Apply associative binary operator `f` to generator `x`."""
    logger.info('++ recurse binary')
    assert n > 0, n
    if n == 1:
        return next(x)
    assert n > 1, n
    m = (n - 1).bit_length() - 1
    c = 2**m
    assert c < n <= 2 * c, (n, c)
    a = recurse_binary_log_space(f, x, c)
    b = recurse_binary_log_space(f, x, n - c)
    logger.info('-- done binary {n} items'.format(n=n))
    return f(a, b)


def recurse_binary(f, x, bdd=None):
    """Recursively traverse binary tree of computation."""
    logger.info('++ recurse binary')
    n = len(x)
    logger.debug('{n} items left to recurse'.format(n=n))
    assert n > 0, n
    if n == 1:
        assert len(x) == 1, x
        return x.pop()
    assert n > 1, n
    # largest power of 2 less than n
    m = (n - 1).bit_length() - 1
    c = 2**m
    assert c < n <= 2 * c, (n, c)
    left = x[:c]
    right = x[c:]
    del x[:]
    a = recurse_binary(f, left, bdd)
    b = recurse_binary(f, right, bdd)
    logger.info(bdd)
    logger.info('-- done recurse binary ({n} items)'.format(n=n))
    return f(a, b)


def _compute_as_binary_tree(f, x):
    """Return result of applying operator `f`.

    In-place computation.
    Non-recursive implementation.
    """
    logger.debug('++ start binary tree')
    assert len(x) > 0
    while len(x) > 1:
        n = len(x)
        logger.debug('Binary at: {n}'.format(n=n))
        k = int(math.floor(n / 2.0))
        # consume the power of 2
        for i in xrange(k):
            j = 2 * i
            a = x[j]
            b = x[j + 1]
            x[i] = f(a, b)
        # has last element ?
        if n % 2 == 1:
            x[k] = x[2 * k]
            # empty tail
            del x[k + 1:]
        else:
            del x[k:]
        n_ = len(x)
        assert n_ == n - k, (n_, n - k)
    assert len(x) == 1, len(x)
    logger.debug('-- done binary tree')
    return x[0]


def _compute_as_binary_tree_simple(f, x):
    """Return result of applying operator `f`.

    Delete level d only after computing level (d + 1).
    Non-recursive implementation.
    """
    logger.debug('++ start binary tree')
    assert len(x) > 0
    while len(x) > 1:
        n = len(x)
        # halve
        r = [f(a, b) for a, b in zip(x[::2], x[1::2])]
        # has last element ?
        if n % 2 == 1:
            r.append(x[-1])
        # empty tail
        x = r
        # assert
        n_ = len(x)
        k = int(math.floor(n / 2.0))
        assert n_ == n - k, (n_, n - k)
    assert len(x) == 1, len(x)
    logger.debug('-- done binary tree')
    return x.pop()


def _linear_operator(f, x):
    """Return result of applying linearly operator `f`."""
    logger.debug('++ start linear operator')
    assert len(x) > 0
    n = len(x)
    for i in xrange(1, n):
        x[0] = f(x[0], x.pop())
    assert len(x) == 1, len(x)
    logger.debug('-- done linear operator')
    return x.pop()


def _linear_operator_simple(f, x):
    """Return result of applying linearly operator `f`."""
    logger.debug('++ start simple linear operator')
    assert len(x) > 0
    u = x[0]
    for v in x[1:]:
        u = f(u, v)
    logger.debug('-- done simple linear operator')
    return u


def test_binary_operators():
    for n in xrange(1, 1500):
        a = range(n)
        f = _plus
        x0 = _compute_as_binary_tree(f, list(a))
        x1 = _compute_as_binary_tree_simple(f, list(a))
        x2 = _linear_operator(f, list(a))
        x3 = _linear_operator_simple(f, list(a))
        x4 = recurse_binary(f, list(a))
        z = sum(a)
        assert x0 == z, (x0, z)
        assert x1 == z, (x1, z)
        assert x2 == z, (x2, z)
        assert x3 == z, (x3, z)
        assert x4 == z, (x4, z)
        print(z)


def _plus(x, y):
    return x + y


def prime(var):
    """Return primed variable."""
    assert not isprimed(var), var
    return var + PRIME


def unprime(var):
    """Return unprimed variable."""
    assert isprimed(var), var
    s = var[:-1]
    assert not isprimed(s), s
    return s


def isprimed(var):
    """Return `True` iff `var` ends with prime."""
    return var[-1] == PRIME


def isinstance_str(s):
    """Raise `AssertionError` if `s` is not a "string"."""
    try:
        s + 's'
    except TypeError:
        return False
    return True
