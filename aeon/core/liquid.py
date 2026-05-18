"""LiquidTerm hierarchy. Re-exports the Rust core (aeon_rs) plus
`liquid_free_vars` (the only Python-side helper still used).
"""

from __future__ import annotations

from aeon_rs import LiquidApp as LiquidApp
from aeon_rs import LiquidHole as LiquidHole
from aeon_rs import LiquidLiteralBool as LiquidLiteralBool
from aeon_rs import LiquidLiteralFloat as LiquidLiteralFloat
from aeon_rs import LiquidLiteralInt as LiquidLiteralInt
from aeon_rs import LiquidLiteralString as LiquidLiteralString
from aeon_rs import LiquidTerm as LiquidTerm
from aeon_rs import LiquidVar as LiquidVar

from aeon.utils.name import Name


def liquid_free_vars(e: LiquidTerm) -> list[Name]:
    if isinstance(e, LiquidVar):
        return [e.name]
    elif isinstance(e, LiquidApp):
        return [e.fun] + [x for arg in e.args for x in liquid_free_vars(arg)]
    else:
        return []
