from __future__ import annotations

from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidVar
from aeon.core.types import t_int
from aeon.verification.smt import smt_valid
from aeon.verification.vcs import Implication
from aeon.verification.vcs import LiquidConstraint

example = Implication(
    "x",
    t_int,
    LiquidApp("==", [LiquidVar("x"), LiquidLiteralInt(3)]),
    LiquidConstraint(LiquidApp(
        "==", [LiquidVar("x"), LiquidLiteralInt(3)])),
)


def test_smt_example3():
    assert smt_valid(example)
