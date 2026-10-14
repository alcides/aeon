"""Exercise the compiled benchmark adapter, including its shape guard."""

from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT


class PSB2FitnessTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from loguru import logger

        logger.remove()
        from aeon.facade.driver import AeonConfig, AeonDriver
        from aeon.synthesis.uis.api import SilentSynthesisUI

        cls.driver = AeonDriver(
            AeonConfig(synthesizer="random_search", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
        )
        errors = list(
            cls.driver.parse(
                aeon_code="""
import PSB2Fitness
import Array

def adapt_int (1 values: (Array Int)) : {errors: (Array Float) | Array.size errors = 200} :=
    PSB2Fitness.per_example_errors values;
def adapt_float (1 values: (Array Float)) : {errors: (Array Float) | Array.size errors = 200} :=
    PSB2Fitness.per_example_errors values;
def adapt_leaders (1 values: (Array Float)) : {errors: (Array Float) | Array.size errors = 50} :=
    PSB2Fitness.per_example_errors_50 values;
"""
            )
        )
        if errors:
            raise AssertionError(errors)
        cls.functions = {}
        for name in ("adapt_int", "adapt_float", "adapt_leaders"):
            namespace = {}
            exec(cls.driver.export(name), namespace)
            cls.functions[name] = namespace[name]

    def test_integer_errors_preserve_each_objective(self):
        errors = list(range(200))
        result = self.functions["adapt_int"](errors)
        self.assertEqual(result, [float(x) for x in errors])
        self.assertTrue(all(isinstance(x, float) for x in result))

    def test_fractional_errors_are_not_truncated(self):
        errors = [i / 8 for i in range(200)]
        self.assertEqual(self.functions["adapt_float"](errors), errors)

    def test_wrong_vector_length_is_rejected(self):
        for count in (0, 1, 199, 201):
            with self.subTest(count=count), self.assertRaisesRegex(ValueError, "200 per-example errors"):
                self.functions["adapt_int"]([0] * count)

    def test_leaders_uses_fifty_objectives(self):
        errors = [i / 8 for i in range(50)]
        self.assertEqual(self.functions["adapt_leaders"](errors), errors)
        for count in (0, 49, 51, 200):
            with self.subTest(count=count), self.assertRaisesRegex(ValueError, "50 per-example errors"):
                self.functions["adapt_leaders"]([0.0] * count)


class PSB2ReferenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from loguru import logger

        logger.remove()
        from aeon.facade.driver import AeonConfig, AeonDriver
        from aeon.synthesis.uis.api import SilentSynthesisUI
        from aeon.backend.python_export import export_function

        cls.functions = {}
        for file, name in (("dice_game.ae", "dice_game"), ("square_digit.ae", "square_digit_unsafe")):
            driver = AeonDriver(AeonConfig("random_search", SilentSynthesisUI(), 0, no_main=True))
            errors = list(driver.parse(str(SOURCE / "examples/PSB2" / file)))
            if errors:
                raise AssertionError(errors)
            # Export the reference directly; do not synthesize or fetch datasets.
            namespace = {}
            exec(export_function(driver.core, name), namespace)
            cls.functions[name] = namespace[name]

    def test_dice_probability_matches_exhaustive_small_dice(self):
        for n in range(1, 7):
            for m in range(1, 7):
                expected = sum(a > b for a in range(1, n + 1) for b in range(1, m + 1)) / (n * m)
                self.assertAlmostEqual(self.functions["dice_game"](n)(m), expected)

    def test_squared_digits_include_zero_and_repeated_digits(self):
        for value, expected in ((0, "0"), (1, "1"), (9119, "811181"), (100, "100")):
            self.assertEqual(self.functions["square_digit_unsafe"](value), expected)


if __name__ == "__main__":
    unittest.main()
