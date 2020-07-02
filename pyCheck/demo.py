import unittest

from pyCheck.pyCheck import provide, runall

# Alternative representation
@provide('{x:Integer | (x >= 0) && (x <= 10)}', '{y:Integer | (y >= 0) && (y <= 10)}', expected='{z:Integer | z == x + y}', repeat=100)
def abs_sum(x, y) :
    # Bug here, remove this if
    if x > 7 or y > 7:
        x = x * y
    return x + y

runall('pyCheck.demo')