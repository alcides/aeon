"""contains_horn must detect horns nested under LiquidApp (e.g. &&(e, κ))."""

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidVar
from aeon.core.types import LiquidHornApplication, t_int
from aeon.utils.name import Name
from aeon.verification.horn import contains_horn


def test_contains_horn_under_and_with_plain_arg():
    kappa = LiquidHornApplication(Name("?", 0), [(LiquidVar(Name("v", 0)), t_int)])
    plain = LiquidLiteralBool(True)
    conj = LiquidApp(Name("&&", 0), [plain, kappa])
    assert contains_horn(conj) is True


def test_contains_horn_plain_app_is_false():
    plain = LiquidApp(Name("==", 0), [LiquidLiteralBool(True), LiquidLiteralBool(True)])
    assert contains_horn(plain) is False
