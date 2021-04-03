from typing import List, Any, Optional, Tuple

from aeon.frontend.parser import parse_term
from aeon.core.types import Type, t_bool, t_int
from aeon.core.liquid import (
    LiquidHole,
    LiquidLiteralBool,
    LiquidLiteralString,
    LiquidTerm,
    LiquidApp,
    LiquidLiteralInt,
    LiquidVar,
)
from aeon.core.substitutions import liquefy
from aeon.verification.vcs import Conjunction, Constraint, Implication, LiquidConstraint


def parse_liquid(t: str) -> LiquidTerm:
    tp = parse_term(t)
    tl = liquefy(tp)
    return tl


def imp(a: Any, b: LiquidConstraint) -> LiquidConstraint:
    if isinstance(a, str):
        a = parse_liquid(a)
    assert isinstance(a, LiquidTerm)
    return Implication("_", t_bool, a, b)


def conj(a: LiquidConstraint, b: LiquidConstraint) -> LiquidConstraint:
    return Conjunction(a, b)


def end(a: str) -> LiquidConstraint:
    if isinstance(a, str):
        a = parse_liquid(a)
    assert isinstance(a, LiquidTerm)
    return LiquidConstraint(a)


def constraint_builder(vs: List[Tuple[str, Type]], exp: LiquidConstraint):
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
