"""Tests for gr1 fragment utilities."""
from omega import gr1
import pytest


def test_split_gr1():
    # init
    f = r'(x > 0) /\ (y + 1 < 2)'
    d = gr1.split_gr1(f)
    t = d['init']
    assert len(t) == 2, t
    s = t[0].flatten()
    assert s == '( x > 0 )', s
    s = t[1].flatten()
    assert s == '( ( y + 1 ) < 2 )', s
    #
    assert d['action'] == list(), d
    assert d['recurrence'] == list(), d
    assert d['persistence'] == list(), d
    # safety
    f = r'[]((x > 0) /\ (z = 3 + y))'
    d = gr1.split_gr1(f)
    assert d['init'] == list(), d
    t = d['action']
    assert len(t) == 1, t
    s = t[0].flatten()
    assert s == r'( ( x > 0 ) /\ ( z = ( 3 + y ) ) )', s
    assert d['recurrence'] == list(), d
    assert d['persistence'] == list(), d
    # recurrence
    f = '[]<>(x > 0)'
    d = gr1.split_gr1(f)
    assert d['init'] == list(), d
    assert d['action'] == list(), d
    t = d['recurrence']
    assert len(t) == 1, t
    s = t[0].flatten()
    assert s == '( x > 0 )', s
    assert d['persistence'] == list(), d
    # all together
    f = r'''
        (x > 0) /\ (y + 1 < 2)
        /\ []( (X y) > 0)
        /\ []<>(z - x <= 0)
        /\ []<>(p => q)
        '''
    d = gr1.split_gr1(f)
    t = d['init']
    assert len(t) == 2, t
    s = t[0].flatten()
    assert s == '( x > 0 )', s
    s = t[1].flatten()
    assert s == '( ( y + 1 ) < 2 )', s
    t = d['action']
    assert len(t) == 1, t
    s = t[0].flatten()
    assert s == '( ( X y ) > 0 )', s
    t = d['recurrence']
    assert len(t) == 2, t
    s = t[0].flatten()
    assert s == '( ( z - x ) <= 0 )', s
    s = t[1].flatten()
    assert s == '( p => q )', s
    assert d['persistence'] == list(), d
    # not in fragment
    with pytest.raises(AssertionError):
        gr1.split_gr1('[]( [] p )')
    with pytest.raises(AssertionError):
        gr1.split_gr1('[] <>( [] p )')
    with pytest.raises(AssertionError):
        gr1.split_gr1(r'(X p ) /\ ( [] p )')
    with pytest.raises(AssertionError):
        gr1.split_gr1(r'[]<> ( x /\ (X y) )')


if __name__ == '__main__':
    test_split_gr1()
