from __future__ import annotations

from typing import Optional
from typing import Tuple

from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidTerm

all_ops = [
    ("==", ("a", "a", "Bool")),
    ("!=", ("a", "a", "Bool")),
    ("<", ("Int", "Int", "Bool")),
    (">", ("Int", "Int", "Bool")),
    ("<=", ("Int", "Int", "Bool")),
    (">=", ("Int", "Int", "Bool")),
    ("-->", ("Bool", "Bool", "Bool")),
    ("&&", ("Bool", "Bool", "Bool")),
    ("||", ("Bool", "Bool", "Bool")),
    ("*", ("Int", "Int", "Int")),
    ("+", ("Int", "Int", "Int")),
    ("/", ("Int", "Int", "Int")),
    ("-", ("Int", "Int", "Int")),
    ("%", ("Int", "Int", "Int")),
    ("!", ("Bool", "Bool")),
]

ops = [x[0] for x in all_ops]


def get_type_of(name: str) -> tuple | None:
    for (op, t) in all_ops:
        if op == name:
            return t
    return None


def mk_liquid_and(e1: LiquidTerm, e2: LiquidTerm):
    if e1 == LiquidLiteralBool(True):
        return e2
    elif e2 == LiquidLiteralBool(True):
        return e1
    elif e1 == LiquidLiteralBool(False):
        return e1
    elif e2 == LiquidLiteralBool(False):
        return e2
    else:
        return LiquidApp("&&", [e1, e2])
