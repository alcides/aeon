"""Deterministic finite-grammar pruning comparison, usable on the old backend.

Run with PYTHONPATH set to the checkout being measured. The one append prefix
has length six; eight available suffixes all have nonnegative length. The goal
has length five. Instrument the argument generator and final verifier calls,
independently of the implementation's own counters.
"""

from __future__ import annotations

import inspect
import json
from unittest.mock import patch

from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, RefinedType, TypeConstructor, t_int
from aeon.synthesis.modules.synquid import engine
from aeon.typechecking.context import TypeConstructorBinder, UninterpretedBinder
from aeon.typechecking.typeinfer import check_type
from aeon.utils.ctx_helpers import built_std_context
from aeon.utils.name import Name


def run(prefix_length: int) -> dict[str, int]:
    def name(s):
        return Name(s, 0)

    def app(op, *args):
        return LiquidApp(name(op), list(args))

    seq = TypeConstructor(name("Seq"))
    ctx = built_std_context()
    ctx.entries.extend(
        [TypeConstructorBinder(seq.name, []), UninterpretedBinder(name("len"), AbstractionType(name("s"), seq, t_int))]
    )
    v, xs, ys = (LiquidVar(name(n)) for n in ("v", "xs", "ys"))

    def length(t):
        return app("len", t)

    nonnegative = RefinedType(name("v"), seq, app(">=", length(v), LiquidLiteralInt(0)))
    result = RefinedType(name("v"), seq, app("==", length(v), app("+", length(xs), length(ys))))
    fn = AbstractionType(name("xs"), nonnegative, AbstractionType(name("ys"), nonnegative, result))
    ctx = ctx.with_var(name("append"), fn)
    for n, size in [("prefix", prefix_length)] + [(f"suffix{i}", i) for i in range(8)]:
        ctx = ctx.with_var(name(n), RefinedType(name("v"), seq, app("==", length(v), LiquidLiteralInt(size))))
    goal = RefinedType(name("v"), seq, app("==", length(v), LiquidLiteralInt(5)))
    counters = {"argument_candidates": 0, "suffix_generators": 0, "full_validations": 0, "solutions": 0}
    calls = 0

    def arguments(*args):
        nonlocal calls
        calls += 1
        if calls == 1:
            names = ["prefix"]
        else:
            counters["suffix_generators"] += 1
            names = [f"suffix{i}" for i in range(8)]
        for n in names:
            counters["argument_candidates"] += 1
            yield Var(name(n))

    options: dict = (
        {"conditionals": False} if "conditionals" in inspect.signature(engine.synthes_memory).parameters else {}
    )
    mem: dict = {}
    with patch.object(engine, "_arg_gen", arguments):
        for term in engine.synthes_memory(ctx, 1, goal, lambda n: n.name != "append", mem, **options):
            counters["full_validations"] += 1
            counters["solutions"] += int(check_type(ctx, term, goal))
    stats = mem.get("synquid_stats")
    counters["partial_rejections"] = stats.partial_rejections if stats is not None else 0
    counters["complete_rejections"] = stats.complete_rejections if stats is not None else 0
    return counters


if __name__ == "__main__":
    print(json.dumps({"impossible_prefix": run(6), "compatible_prefix": run(3)}, indent=2))
