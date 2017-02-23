"""Tests for gr1 fragment utilities."""
from nose.tools import assert_raises
from omega import gr1


def test_split_gr1():
    # init
    f = '(x > 0) & (y + 1 < 2)'
    d = gr1.split_gr1(f)
    assert d['init'] == ['( ( x > 0 ) /\ ( ( y + 1 ) < 2 ) )'], d
    assert d['G'] == ['( True /\ True )'], d
    assert d['GF'] == [], d
    # safety
    f = '[]((x > 0) & (z = 3 + y))'
    d = gr1.split_gr1(f)
    assert d['init'] == ['True'], d
    assert d['G'] == ['( ( x > 0 ) /\ ( z = ( 3 + y ) ) )'], d
    assert d['GF'] == [], d
    # recurrence
    f = '[]<>(x > 0)'
    d = gr1.split_gr1(f)
    assert d['init'] == ['True'], d
    assert d['G'] == ['True'], d
    assert d['GF'] == ['( x > 0 )'], d
    # all together
    f = (
        '(x > 0) /\ (y + 1 < 2) /\ '
        '[]( (X y) > 0) /\ '
        '[]<>((z - x <= 0) \/ (p => q))')
    d = gr1.split_gr1(f)
    s = (
        '( ( ( ( x > 0 ) /\ ( ( y + 1 ) < 2 ) ) '
        '/\ True ) /\ True )')
    assert d['init'] == [s], d
    assert d['G'] == [
        '( ( ( True /\ True ) /\ ( ( X y ) > 0 ) ) /\ True )'], d
    assert d['GF'] == [
        '( ( ( z - x ) <= 0 ) \/ ( p => q ) )'], d
    # not in fragment
    with assert_raises(AssertionError):
        gr1.split_gr1('[]( [] p )')
    with assert_raises(AssertionError):
        gr1.split_gr1('<>( [] p )')
    with assert_raises(AssertionError):
        gr1.split_gr1('(X p ) /\ ( [] p )')
    with assert_raises(AssertionError):
        gr1.split_gr1('[]<> ( x /\ (X y) )')


if __name__ == '__main__':
    test_split_gr1()
