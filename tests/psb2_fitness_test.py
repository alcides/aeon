"""Exercise the compiled benchmark adapter, including arbitrary objective counts."""

from pathlib import Path
import unittest

import pytest

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

def adapt_int (1 values: (Array Int)) : {errors: (Array Float) | Array.size errors = Array.size values} :=
    PSB2Fitness.per_example_errors_int values;
def adapt_float (1 values: (Array Float)) : {errors: (Array Float) | Array.size errors = Array.size values} :=
    PSB2Fitness.per_example_errors values;
def adapt_leaders (1 values: (Array Float)) : {errors: (Array Float) | Array.size errors = Array.size values} :=
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

    def test_arbitrary_objective_counts(self):
        for count in (0, 1, 3, 49, 50, 51, 199, 200, 201, 257):
            for name in ("adapt_int", "adapt_float", "adapt_leaders"):
                with self.subTest(count=count, adapter=name):
                    values = list(range(count)) if name == "adapt_int" else [i / 8 for i in range(count)]
                    self.assertEqual(self.functions[name](values), [float(v) for v in values])


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
            errors = list(driver.parse(str(SOURCE / "examples/benchmarks/psb2" / file)))
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


@pytest.mark.parametrize("count", [1, 7, 51, 257])
def test_adapter_preserves_declared_decorator_objectives(count):
    from tests.driver import check_and_return_core
    from aeon.backend.evaluator import eval as evaluate
    from aeon.synthesis.fitness_eval import set_program_tail, as_objective_vector
    from aeon.core.terms import Var

    core, _, context, metadata = check_and_return_core(f"""
import Array;
import PSB2Fitness;
@multi_minimize_float(PSB2Fitness.per_example_errors (Array.mk_repeat {count} 0.25), {count})
def candidate (x:Int):Int := x;
""")
    goals = [goal for entry in metadata.values() for goal in entry.get("goals", [])]
    assert len(goals) == 1 and goals[0].length == count
    values = evaluate(set_program_tail(core, Var(goals[0].function)), context)
    assert as_objective_vector(values, count) == [0.25] * count
