import unittest

from pyCheck.pyCheck import provide

# Alternative representation
#@test('({x:Integer where x >= 0 && x <= 10}, {y:Integer where y < 0}) -> {z:Integer where z == x - y}', repeat = 100)
def abs_sum(x, y) :
    if y < 0: 
        y = abs(y)
    # Bug here, remove this if
    if x == 5:
        x = 0
    return x + y

    

@provide('{x:Integer where x >= 0 && x <= 10}', '{y:Integer where y < 0}', repeat=100)
def test_restricted_x(x, y):
    result = abs_sum(x, y)
    expected = x - y

    assert(result == expected)

# Wanted to do this in unittest, but have problems with self argument on decorator
'''
class TestAbsSum(unittest.TestCase):
    # pytest-quickcheck
    @check('{x:int where x >= 0 and x <= 10}', '{y:int where y < 0}', repeat=100)
    def test_restricted_x(self, x, y):
        self.assertEquals(abs_sum(x, y), x - y)
'''