import unittest
import random

from aeon.frontend_core import expr
from aeon.evaluation.metrics.distance import compare_trees


class TestDiversity(unittest.TestCase):
    def parse(self, text):
        return expr.parse(text)

    def diff_formula(self, value1, value2):
        return (1 - pow(0.99, abs(value1 - value2)))

    def test_literals(self):
        ast1 = self.parse('10')
        ast2 = self.parse('30')

        expected = self.diff_formula(ast1.value, ast2.value)
        result = compare_trees(ast1, ast2)

        self.assertEqual(expected, result)


if __name__ == '__main__':
    unittest.main()
