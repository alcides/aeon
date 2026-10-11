"""Aeon adapter for BUSTLE: scalar PBE with learned bottom-up guidance."""

from __future__ import annotations

import os
import time
from collections import Counter
from collections.abc import Callable, Sequence
from pathlib import Path
from typing import Any

from loguru import logger

from aeon.core.terms import Literal, Term, Var
from aeon.core.types import Type, t_bool, t_int, t_string
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer, SynthesisNotSuccessful
from aeon.synthesis.modules.bustle.model import GuidanceModel
from aeon.synthesis.modules.bustle.search import Operation, SearchStats, Value, enumerate_values
from aeon.synthesis.modules.bustle.signatures import MAX_INPUTS, Scalar, valid_scalar
from aeon.synthesis.modules.fta.synthesizer import FTASynthesizer
from aeon.synthesis.modules.symetric.synthesizer import base_key
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

SCALAR_TYPES = {"Int": t_int, "Bool": t_bool, "String": t_string}
# Monomorphize prelude operators only at meaningful types, never String arithmetic.
NUMERIC = {"+", "-", "*", "/", "%", "<", ">", "<=", ">="}
EQUALITY = {"==", "!="}


def extract_constants(columns: Sequence[Sequence[Scalar]], outputs: Sequence[Scalar]) -> dict[str, list[Scalar]]:
    """Paper-style common literals plus repeated short substrings of examples."""
    strings = [v for column in [*columns, outputs] for v in column if type(v) is str]
    symbols = [s for s in " ,.!?()[]<>-_/$#:;@%0" if any(s in v for v in strings)]
    counts: Counter[str] = Counter()
    for string in strings:
        # At most one vote per example string, rather than counting repeated
        # occurrences within a single string as separate evidence.
        counts.update(
            {string[i : i + n] for n in range(2, min(16, len(string)) + 1) for i in range(len(string) - n + 1)}
        )
    repeated = sorted((s for s, count in counts.items() if count >= 2), key=lambda s: (-counts[s], -len(s), s))[:32]
    return {"Int": [0, 1, 2, 3, 99], "Bool": [False, True], "String": list(dict.fromkeys(["", *symbols, *repeated]))}


class BustleSynthesizer(Synthesizer):
    def __init__(
        self,
        model_path: str | Path | None = None,
        *,
        guided: bool = True,
        max_weight: int = 40,
        max_values: int = 20_000,
    ):
        self.model_path = model_path
        self.guided = guided
        self.max_weight = max_weight
        self.max_values = max_values
        self.stats = SearchStats()

    def computations(self, primitives: Any) -> dict[str, Any]:
        # Example consistency is decided from intermediate vectors in process;
        # the existing entrypoint supplies pbe_probe for library evaluation.
        return {}

    def synthesize(
        self,
        ctx: TypingContext,
        type: Type,
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        fun_name: Name,
        metadata: Metadata,
        budget: float = 60,
        ui: SynthesisUI = SynthesisUI(),
        output_value: Callable[[Term], object] | None = None,
    ) -> Term:
        start = time.monotonic()
        goal = base_key(type)
        if goal not in SCALAR_TYPES:
            raise SynthesisNotSuccessful("bustle: result must be Int, Bool, or String")
        entry = metadata.get(fun_name, {})
        rows = entry.get("io_examples", [])
        params = entry.get("io_params", [])
        probe = entry.get("pbe_probe")
        if not rows or not callable(probe):
            raise SynthesisNotSuccessful(f"bustle: {fun_name.name} needs literal @example I/O pairs")
        if not 1 <= len(params) <= MAX_INPUTS:
            raise SynthesisNotSuccessful(f"bustle: supports 1–{MAX_INPUTS} scalar value parameters")
        if (
            len(entry.get("goals", [])) > len(entry.get("examples", []))
            or entry.get("example_io_miss")
            or entry.get("property")
        ):
            raise SynthesisNotSuccessful(
                "bustle: supports literal I/O goals, not additional optimization or relational examples"
            )
        var_types = dict(ctx.vars())
        param_keys = [base_key(var_types[p]) for p in params]
        if any(key not in SCALAR_TYPES for key in param_keys):
            raise SynthesisNotSuccessful("bustle: inputs must be Int, Bool, or String")
        if any(len(args) != len(params) for args, _ in rows):
            raise SynthesisNotSuccessful("bustle: inconsistent example arity")
        columns = [tuple(args[i] for args, _ in rows) for i in range(len(params))]
        expected = tuple(out for _, out in rows)
        if not all(valid_scalar(v, key) for column, key in zip(columns, param_keys) for v in column) or not all(
            valid_scalar(v, goal) for v in expected
        ):
            raise SynthesisNotSuccessful(
                "bustle: examples must match their scalar types (strings <=256 chars, |integers| <=10^9)"
            )
        model: GuidanceModel | None = None
        if self.guided:
            path = self.model_path or os.environ.get("AEON_BUSTLE_MODEL")
            try:
                model = GuidanceModel.load(path) if path else GuidanceModel.load()
            except (OSError, ValueError, KeyError, TypeError) as exc:
                raise SynthesisNotSuccessful(f"bustle: cannot load trained guidance: {exc}") from exc
        logger.log("SYNTHESIZER", "bustle: {}", "learned guidance" if model is not None else "unguided baseline")
        atoms = [Value(Var(p), key, values) for p, key, values in zip(params, param_keys, columns)]
        constants = extract_constants(columns, expected)
        for key, values in constants.items():
            atoms.extend(Value(Literal(v, SCALAR_TYPES[key]), key, (v,) * len(rows)) for v in values)

        collector = FTASynthesizer()
        builders, leaves = collector._collect(ctx, set(SCALAR_TYPES.values()), fun_name)
        for key, terms in leaves.items():
            if key not in SCALAR_TYPES:
                continue
            for term in terms:
                if term.name in params or term.name.name.startswith("_"):
                    continue
                try:
                    observed_values = tuple(probe(term, list(args)) for args, _ in rows)
                    atoms.append(Value(term, key, observed_values))
                except Exception:
                    continue
        operations: list[Operation] = []
        for key, components in builders.items():
            if key not in SCALAR_TYPES:
                continue
            for comp in components:
                if not 1 <= len(comp.arg_keys) <= 3 or any(k not in SCALAR_TYPES for k in comp.arg_keys):
                    continue
                name = comp.name.name
                if name.startswith("_") or (name in NUMERIC and comp.arg_keys != ("Int", "Int")):
                    continue
                if name in EQUALITY and len(set(comp.arg_keys)) != 1:
                    continue
                head = collector._head(comp)
                try:
                    function = probe(head, list(rows[0][0]))
                    if not callable(function):
                        continue
                except Exception:
                    continue

                def execute(arguments: tuple[Scalar, ...], function=function) -> Scalar:
                    result = function
                    for argument in arguments:
                        result = result(argument)
                    return result

                operations.append(Operation(head, comp.arg_keys, key, execute))
        for key in SCALAR_TYPES:
            operations.append(
                Operation(
                    Var(Name("if", 0)),
                    ("Bool", key, key),
                    key,
                    lambda args: args[1] if args[0] else args[2],
                    conditional=True,
                )
            )

        def accept(value: Value) -> bool:
            if value.key != goal or value.outputs != expected:
                return False
            try:
                return validate(value.term)
            except Exception:
                return False

        self.stats = SearchStats()
        result = enumerate_values(
            atoms,
            operations,
            columns,
            expected,
            accept=accept,
            predict=model.predict if model is not None else None,
            deadline=start + budget,
            max_weight=self.max_weight,
            max_values=self.max_values,
            stats=self.stats,
        )
        ui.progress(self.stats.generated, self.stats.unique, time.monotonic() - start)
        if result is None:
            raise SynthesisNotSuccessful(
                f"bustle: {self.stats.stopped}; no example-consistent, well-typed body after {self.stats.generated} expressions (weight {self.stats.final_weight})"
            )
        ui.register(result.term, [0.0], time.monotonic() - start, True)
        return result.term
