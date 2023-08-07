from __future__ import annotations

from typing import Tuple

from aeon.core.types import Type
from aeon.typechecking.context import TypingContext


def unify(ctx: TypingContext, sub: Type, sup: Type) -> tuple[bool, dict]:
    return (True, {})
