from __future__ import annotations

from typing import Any
from typing import List
from typing import Optional
from typing import Tuple
from typing import Union

from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidHole
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import liquefy
from aeon.core.types import t_bool
from aeon.core.types import t_int
from aeon.core.types import Type
from aeon.frontend.parser import parse_term
from aeon.verification.vcs import Conjunction
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import Implication
from aeon.verification.vcs import LiquidConstraint


def parse_liquid(t: str) -> LiquidTerm:
    tp = parse_term(t)
    tl = liquefy(tp)
    return tl


def imp(a: str | LiquidTerm, b: Constraint) -> Constraint:
    if isinstance(a, str):
        a = parse_liquid(a)
    assert isinstance(a, LiquidTerm)
    return Implication("_", t_bool, a, b)


def conj(a: Constraint, b: Constraint) -> Constraint:
    return Conjunction(a, b)


def end(a: str | LiquidTerm) -> LiquidConstraint:
    if isinstance(a, str):
        a = parse_liquid(a)
    assert isinstance(a, LiquidTerm)
    return LiquidConstraint(a)


def constraint_builder(vs: list[tuple[str, Type]], exp: Constraint):
    for (n, t) in vs[::-1]:
        exp = Implication(n, t, LiquidLiteralBool(True), exp)
    return exp


def get_abs_example() -> Constraint:
    hole = LiquidHole(
        "k",
        [(LiquidVar("x"), "Int"), (LiquidVar("v"), "Int")],
    )
    hole2 = LiquidHole(
        "k",
        [(LiquidVar("y"), "Int"), (LiquidVar("z"), "Int")],
    )

    ap = constraint_builder(
        vs=[("x", t_int), ("c", t_bool), ("v", t_int)],
        exp=imp(
            "c == (0 <= x)",
            conj(
                imp(
                    "c",
                    imp("v == x", end(hole)),
                ),
                imp("!c", imp("v == (0 - x)", end(hole))),
            ),
        ),
    )

    cp = constraint_builder(
        vs=[("y", t_int), ("z", t_int), ("c", t_bool), ("b", t_bool)],
        exp=imp(hole2, imp("c == (0 <= z)", imp("b == c", end("b")))),
    )

    return conj(ap, cp)
