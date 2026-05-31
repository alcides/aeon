"""LiquidTerm hierarchy — re-export of the Rust core (``aeon-rs/src/liquid.rs``).

The Rust pyclasses mirror master's Python dataclasses one-for-one,
including ``LiquidLiteralUnit`` (the single inhabitant of the Unit type,
with its own SMT sort).
"""

from __future__ import annotations

from aeon.utils.name import Name

from aeon_rs import LiquidApp as LiquidApp
from aeon_rs import LiquidHole as LiquidHole
from aeon_rs import LiquidLiteralBool as LiquidLiteralBool
from aeon_rs import LiquidLiteralFloat as LiquidLiteralFloat
from aeon_rs import LiquidLiteralInt as LiquidLiteralInt
from aeon_rs import LiquidLiteralString as LiquidLiteralString
from aeon_rs import LiquidLiteralUnit as LiquidLiteralUnit
from aeon_rs import LiquidTerm as LiquidTerm
from aeon_rs import LiquidVar as LiquidVar
from aeon_rs import ensure_liqterm as ensure_liqterm
from aeon_rs import is_safe_for_application as is_safe_for_application


def liquid_free_vars(e: LiquidTerm) -> list[Name]:
    if isinstance(e, LiquidVar):
        return [e.name]
    elif isinstance(e, LiquidApp):
        return [e.fun] + [x for arg in e.args for x in liquid_free_vars(arg)]
    else:
        return []


__all__ = [
    "LiquidApp",
    "LiquidHole",
    "LiquidLiteralBool",
    "LiquidLiteralFloat",
    "LiquidLiteralInt",
    "LiquidLiteralString",
    "LiquidLiteralUnit",
    "LiquidTerm",
    "LiquidVar",
    "ensure_liqterm",
    "is_safe_for_application",
    "liquid_free_vars",
]
