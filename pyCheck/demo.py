import unittest

from pyCheck.pyCheck import provide

# Alternative representation
#@test('({x:Integer where x >= 0 && x <= 10}, {y:Integer where y < 0}) -> {z:Integer where z == x - y}', repeat = 100)
def abs_sum(x, y) :
    # Bug here, remove this if
    if x > 7 or y > 7:
        x = x * y
    return x + y

    

@provide('{x:Integer | (x >= 0) && (x <= 10)}', '{y:Integer | (y >= 0) && (y <= 10)}', expected='{z:Integer | z == x + y}', repeat=100)
def test_restricted_x(x, y):
    result = abs_sum(x, y)
    return result






# Wanted to do this in unittest, but have problems with self argument on decorator
'''
class TestAbsSum(unittest.TestCase):
    # pytest-quickcheck
    @provide('{x:int where x >= 0 and x <= 10}', '{y:int where y < 0}', repeat=100)
    def test_restricted_x(self, x, y):
        self.assertEquals(abs_sum(x, y), x - y)
'''