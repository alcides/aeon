"""Runtime evaluation of liquid refinement predicates (issue #443).

Deliberately partial: refinements mentioning symbols listed in the
``uninterpreted`` dictionary cannot be checked at run time and are skipped.
Runtime-callable symbols are resolved through a separate ``runtime`` dictionary
so each name maps to at most one implementation.
"""

from __future__ import annotations

from typing import Any

from aeon.core.liquid import (
    LiquidApp,
    LiquidLiteralBool,
    LiquidLiteralFloat,
    LiquidLiteralInt,
    LiquidLiteralString,
    LiquidTerm,
    LiquidVar,
)
from aeon.core.types import Type
from aeon.utils.name import Name


class UnevaluableLiquid(Exception):
    """Predicate fragment outside the runtime interpreter."""


class UninterpretedInLiquid(Exception):
    """Predicate mentions an uninterpreted symbol — no runtime meaning."""


_BINOPS: dict[str, Any] = {
    "==": lambda a, b: a == b,
    "!=": lambda a, b: a != b,
    "<": lambda a, b: a < b,
    "<=": lambda a, b: a <= b,
    ">": lambda a, b: a > b,
    ">=": lambda a, b: a >= b,
    "+": lambda a, b: a + b,
    "-": lambda a, b: a - b,
    "*": lambda a, b: a * b,
    "&&": lambda a, b: bool(a) and bool(b),
    "||": lambda a, b: bool(a) or bool(b),
    "-->": lambda a, b: (not bool(a)) or bool(b),
}


def eval_liquid(
    term: LiquidTerm,
    env: dict[Name, Any],
    *,
    uninterpreted: dict[str, Type],
    runtime: dict[str, Any],
) -> Any:
    if isinstance(term, LiquidVar):
        if term.name not in env:
            raise UnevaluableLiquid(f"unbound liquid variable {term.name}")
        return env[term.name]
    if isinstance(term, LiquidLiteralBool):
        return term.value
    if isinstance(term, LiquidLiteralInt | LiquidLiteralFloat | LiquidLiteralString):
        return term.value
    if isinstance(term, LiquidApp):
        head = term.fun.name
        if head in uninterpreted:
            raise UninterpretedInLiquid(head)
        if head == "!" and len(term.args) == 1:
            return not bool(eval_liquid(term.args[0], env, uninterpreted=uninterpreted, runtime=runtime))
        if head in ("/", "%") and len(term.args) == 2:
            a = eval_liquid(term.args[0], env, uninterpreted=uninterpreted, runtime=runtime)
            b = eval_liquid(term.args[1], env, uninterpreted=uninterpreted, runtime=runtime)
            if not isinstance(a, int) or not isinstance(b, int) or b == 0:
                raise UnevaluableLiquid("non-integral or zero division")
            q = int(a / b)
            return q if head == "/" else a - b * q
        fn = _BINOPS.get(head)
        if fn is not None and len(term.args) == 2:
            return fn(
                eval_liquid(term.args[0], env, uninterpreted=uninterpreted, runtime=runtime),
                eval_liquid(term.args[1], env, uninterpreted=uninterpreted, runtime=runtime),
            )
        callee = runtime.get(head)
        if callee is None:
            raise UnevaluableLiquid(f"unknown liquid head {head!r}")
        args = [eval_liquid(a, env, uninterpreted=uninterpreted, runtime=runtime) for a in term.args]
        return callee(*args)
    raise UnevaluableLiquid(f"unsupported liquid form {type(term).__name__}")


def eval_liquid_bool(
    term: LiquidTerm,
    env: dict[Name, Any],
    *,
    uninterpreted: dict[str, Type],
    runtime: dict[str, Any],
) -> bool:
    try:
        return bool(eval_liquid(term, env, uninterpreted=uninterpreted, runtime=runtime))
    except (TypeError, ValueError, ZeroDivisionError, OverflowError) as exc:
        raise UnevaluableLiquid(str(exc)) from exc
