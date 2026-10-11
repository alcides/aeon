"""Aeon adapter for BUSTLE: scalar and structural ADT PBE with learned bottom-up guidance."""

from __future__ import annotations

import os
import time
from collections import Counter
from collections.abc import Callable, Sequence
from pathlib import Path
from typing import Any

from loguru import logger

from aeon.core.terms import Literal, Term, TypeApplication, Var
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    RefinementPolymorphism,
    Type,
    TypeConstructor,
    TypePolymorphism,
    t_bool,
    t_int,
    t_string,
)
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer, SynthesisNotSuccessful
from aeon.synthesis.modules.bustle.model import GuidanceModel
from aeon.synthesis.modules.bustle.search import Operation, SearchStats, Value, enumerate_values
from aeon.synthesis.modules.bustle.signatures import MAX_INPUTS, Scalar
from aeon.synthesis.modules.fta.synthesizer import FTASynthesizer
from aeon.synthesis.modules.symetric.synthesizer import base_key, _peel
from aeon.synthesis.grammar.poly import monomorphize_poly_type
from aeon.synthesis.uis.api import SynthesisUI
from aeon.synthesis.modules.bustle.values import valid_value
from aeon.verification.constructor_registry import get_constructor_groups
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
        groups = get_constructor_groups()
        supported = dict(SCALAR_TYPES)

        def collect_types(ty: Type) -> None:
            if isinstance(ty, RefinedType):
                collect_types(ty.type)
            elif isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
                collect_types(ty.body)
            elif isinstance(ty, AbstractionType):
                collect_types(ty.var_type)
                collect_types(ty.type)
            elif isinstance(ty, TypeConstructor):
                for argument in ty.args:
                    collect_types(argument)
                if ty.name.name in groups and all(base_key(a) in supported for a in ty.args):
                    supported[base_key(ty)] = ty

        collect_types(type)
        for _, ty in ctx.vars():
            collect_types(ty)
        if goal not in supported:
            raise SynthesisNotSuccessful("bustle: result must be Int, Bool, or String, or a supported registered ADT")
        collector = FTASynthesizer()
        builders, leaves = collector._collect(ctx, set(supported.values()), fun_name)
        schemas: dict[str, dict[str, tuple[str, ...]]] = {key: {} for key in supported if key not in SCALAR_TYPES}
        polymorphic_leaves: list[tuple[str, Term]] = []
        # FTA's collector omits polymorphic nullary constructors. Instantiate
        # these explicitly, e.g. nil{Int} : List Int, without admitting opaque
        # or unregistered values as ADTs.
        for constructor_name, ty in ctx.concrete_vars():
            if not isinstance(ty, TypePolymorphism):
                continue
            if not any(constructor_name.name in tags for tags in groups.values()):
                continue
            for body, type_arguments in monomorphize_poly_type(ty, set(supported.values())):
                arguments, result_type = _peel(body)
                result_key = base_key(result_type)
                if arguments or result_key not in schemas:
                    continue
                head: Term = Var(constructor_name)
                for argument in type_arguments:
                    head = TypeApplication(head, argument)
                schemas[result_key][constructor_name.name] = ()
                polymorphic_leaves.append((result_key, head))
        for key in schemas:
            tags = groups[supported[key].name.name]
            for component in builders.get(key, []):
                if component.name.name in tags and all(k in supported for k in component.arg_keys):
                    schemas[key][component.name.name] = component.arg_keys
            for leaf in leaves.get(key, []):
                if leaf.name.name in tags:
                    schemas[key][leaf.name.name] = ()

        def valid(value: object, key: str) -> bool:
            return valid_value(value, key, schemas)

        entry = metadata.get(fun_name, {})
        rows = entry.get("constructor_io_examples") or entry.get("io_examples", [])
        params = entry.get("io_params", [])
        probe = entry.get("pbe_probe")
        if not rows or not callable(probe):
            raise SynthesisNotSuccessful(f"bustle: {fun_name.name} needs literal @example I/O pairs")
        if not 1 <= len(params) <= MAX_INPUTS:
            raise SynthesisNotSuccessful(f"bustle: supports 1–{MAX_INPUTS} scalar/ADT value parameters")
        if (
            len(entry.get("goals", [])) > len(entry.get("examples", []))
            or len(rows) != len(entry.get("examples", []))
            or entry.get("property")
        ):
            raise SynthesisNotSuccessful(
                "bustle: supports literal I/O goals, not additional optimization or relational examples"
            )
        var_types = dict(ctx.vars())
        param_keys = [base_key(var_types[p]) for p in params]
        if any(key not in supported for key in param_keys):
            raise SynthesisNotSuccessful("bustle: inputs must be scalars or supported registered ADTs")
        if any(len(args) != len(params) for args, _ in rows):
            raise SynthesisNotSuccessful("bustle: inconsistent example arity")
        columns = [tuple(args[i] for args, _ in rows) for i in range(len(params))]
        expected = tuple(out for _, out in rows)
        if not all(valid(v, key) for column, key in zip(columns, param_keys) for v in column) or not all(
            valid(v, goal) for v in expected
        ):
            raise SynthesisNotSuccessful("bustle: examples must match their scalar/ADT types and structural bounds")
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

        for key, head in polymorphic_leaves:
            try:
                observed_values = tuple(probe(head, list(args)) for args, _ in rows)
                atoms.append(Value(head, key, observed_values))
            except Exception:
                continue

        for key, terms in leaves.items():
            if key not in supported:
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
            if key not in supported:
                continue
            for comp in components:
                if not 1 <= len(comp.arg_keys) <= 3 or any(k not in supported for k in comp.arg_keys):
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
        for key in supported:
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
            valid=valid,
        )
        ui.progress(self.stats.generated, self.stats.unique, time.monotonic() - start)
        if result is None:
            raise SynthesisNotSuccessful(
                f"bustle: {self.stats.stopped}; no example-consistent, well-typed body after {self.stats.generated} expressions (weight {self.stats.final_weight})"
            )
        ui.register(result.term, [0.0], time.monotonic() - start, True)
        return result.term
