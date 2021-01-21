from aeon.core.types import t_int
from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidVar
from aeon.verification.vcs import Implication, LiquidConstraint
from aeon.verification.smt import smt_valid

example = Implication(
    "x",
    t_int,
    LiquidApp("==", [LiquidVar("x"), LiquidLiteralInt(3)]),
    LiquidConstraint(LiquidApp(
        "==", [LiquidVar("x"), LiquidLiteralInt(3)])),
)


def test_smt_example3():
    assert smt_valid(example)
