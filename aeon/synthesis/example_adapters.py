"""Checked datasets shared by example-driven synthesis backends.

Property equalities provide labels only when one side is a fully applied target
and the other side can be evaluated independently. Relational properties and
optimization objectives remain validation/ranking goals, never invented labels.
The sampled properties must still be checked on every completed candidate.
"""

from __future__ import annotations

from dataclasses import replace
from time import monotonic
from typing import Any

from aeon.backend.evaluator import EvaluationContext, eval as evaluate
from aeon.core.substitutions import substitution
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    Let,
    Rec,
    RefinementApplication,
    Term,
    TypeApplication,
    Var,
)
from aeon.synthesis.api import InvalidIndividualException, UnsupportedSynthesisGoal
from aeon.synthesis.evaluation_pool import EvaluationPool, OK
from aeon.synthesis.identification import term_has_holes
from aeon.synthesis.pbt.runner import PropertyCorpus, PropertySpec, _term_references
from aeon.synthesis.refinement_examples import derive_refinement_examples
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name
from aeon.verification.constructor_registry import get_constructor_fields


def _unwrap(term: Term) -> Term:
    while isinstance(term, (Annotation, TypeApplication, RefinementApplication)):
        term = term.expr if isinstance(term, Annotation) else term.body
    return term


def _call(term: Term) -> tuple[Term, list[Term]]:
    arguments = []
    term = _unwrap(term)
    while isinstance(term, Application):
        arguments.append(term.arg)
        term = _unwrap(term.fun)
    return term, list(reversed(arguments))


def _equations(term: Term, target: Name, arity: int):
    """Only unconditional equalities (possibly conjoined) imply exact labels."""
    term = _unwrap(term)
    if isinstance(term, Let):
        yield from _equations(substitution(term.body, term.var_value, term.var_name), target, arity)
        return
    operator, operands = _call(term)
    if not isinstance(operator, Var) or len(operands) != 2:
        return
    if operator.name.name == "&&":
        for operand in operands:
            yield from _equations(operand, target, arity)
    elif operator.name.name == "==":
        for call_side, output in (operands, list(reversed(operands))):
            function, inputs = _call(call_side)
            if isinstance(function, Var) and function.name == target and len(inputs) == arity:
                yield inputs, output


def _data(value: Any, depth: int = 0) -> bool:
    if type(value) in (int, float, bool, str):
        return True
    if depth >= 16 or not isinstance(value, tuple) or not value or not isinstance(value[0], str):
        return False
    fields = get_constructor_fields(value[0])
    return fields is not None and len(fields) == len(value) - 1 and all(_data(v, depth + 1) for v in value[1:])


def _legacy_data(value: Any) -> Any:
    """Keep Contata's existing flattened List encoding separate from ADT trees."""
    if isinstance(value, tuple):
        if value == ("List_nil",):
            return ()
        if len(value) == 3 and value[0] == "List_cons":
            tail = _legacy_data(value[2])
            if isinstance(tail, tuple):
                return (_legacy_data(value[1]), *tail)
    return value


def _append_rows(existing: list, added: list) -> list:
    """Remove identical observations, preserving contradictory labels."""
    result = list(existing)
    seen = {repr(row) for row in result}
    for row in added:
        key = repr(row)
        if key not in seen:
            seen.add(key)
            result.append(row)
    return result


def derive_property_examples(
    program: Term,
    evaluation_ctx: EvaluationContext,
    function: Name,
    corpora: list[PropertyCorpus],
    *,
    budget: float = 2.0,
    max_examples: int = 64,
) -> dict[str, Any]:
    """Evaluate independent sides of sampled equalities in bounded workers.

    The worker receives only definitions needed by each expression. Unfinished
    targets and all helpers depending on them are rejected before evaluation;
    unrelated eager example/objective helpers are never executed.
    """
    deadline = monotonic() + budget
    bindings: list[Let | Rec] = []
    current = program
    while isinstance(current, (Let, Rec)):
        bindings.append(current)
        current = current.body
    definitions = {binding.var_name: binding.var_value for binding in bindings}
    body = definitions.get(function)
    parameters = []
    while isinstance(body, Abstraction):
        parameters.append(body.var_name)
        body = body.body
    if body is None or budget <= 0 or not corpora:
        return {}
    forbidden = {name for name, value in definitions.items() if term_has_holes(value)} | {function}

    def independent(expression: Term) -> Term:
        pending = list(_term_references(expression))
        needed: set[Name] = set()
        while pending:
            name = pending.pop()
            if name in forbidden:
                raise InvalidIndividualException()
            if name in needed:
                continue
            needed.add(name)
            if name in definitions:
                pending.extend(_term_references(definitions[name]))
        result = expression
        for binding in reversed(bindings):
            if binding.var_name in needed:
                result = replace(binding, body=result)
        return result

    pool = EvaluationPool(
        independent, {"value": lambda expression: evaluate(expression, evaluation_ctx)}, budget_eval=min(0.1, budget)
    )
    rows: list = []
    try:
        for corpus in corpora:
            assertion = definitions.get(corpus.spec.name)
            property_parameters = []
            while isinstance(assertion, Abstraction):
                property_parameters.append(assertion.var_name)
                assertion = assertion.body
            if assertion is None:
                continue
            for case in corpus.cases:
                if len(case) != len(property_parameters):
                    continue
                instantiated = assertion
                for name, argument in zip(property_parameters, case):
                    instantiated = substitution(instantiated, argument, name)
                for inputs, expected in _equations(instantiated, function, len(parameters)):
                    values = []
                    for expression in [*inputs, expected]:
                        if monotonic() >= deadline or len(rows) >= max_examples:
                            return _property_metadata(rows, parameters)
                        status, value = pool.run(expression).get("value", ("error", None))
                        if status != OK or not _data(value):
                            break
                        values.append(value)
                    if len(values) == len(inputs) + 1:
                        rows = _append_rows(rows, [(values[:-1], values[-1])])
    finally:
        pool.close()
    return _property_metadata(rows, parameters)


def _property_metadata(rows: list, parameters: list[Name]) -> dict[str, Any]:
    if not rows:
        return {}
    numeric = [[*inputs, output] for inputs, output in rows if all(type(v) in (int, float) for v in [*inputs, output])]
    return {
        "property_examples": rows,
        "constructor_io_examples": rows,
        "io_examples": [([_legacy_data(v) for v in inputs], _legacy_data(output)) for inputs, output in rows],
        "io_params": parameters,
        **({"training_data": numeric} if numeric else {}),
    }


def adapt_example_metadata(
    ctx: TypingContext,
    ectx: EvaluationContext,
    program: Term,
    function: Name,
    entry: dict[str, Any],
    corpora: list[PropertyCorpus],
    *,
    hole_name: Name | None = None,
    budget: float = 2.0,
    requires_examples: bool = True,
) -> dict[str, Any]:
    """Build local metadata from CSV, property equalities, then refinements."""
    started = monotonic()
    result = dict(entry)
    if entry.get("csv_examples"):
        for key in ("io_examples", "constructor_io_examples"):
            result[key] = _append_rows(result.get(key, []), entry["csv_examples"])
    assertions = [PropertyCorpus(PropertySpec(example.function, (), 1), ((),)) for example in entry.get("examples", [])]
    for samples, marker in ((assertions, "evaluated_examples"), (corpora, "property_examples")):
        generated = derive_property_examples(
            program, ectx, function, samples, budget=max(0.0, budget - (monotonic() - started))
        )
        if "property_examples" in generated:
            generated[marker] = generated.pop("property_examples")
        for key, value in generated.items():
            result[key] = value if key == "io_params" else _append_rows(result.get(key, []), value)
    if requires_examples and not any(
        result.get(key) for key in ("training_data", "io_examples", "constructor_io_examples", "tactic_scripts")
    ):
        try:
            result.update(
                derive_refinement_examples(
                    ctx, program, function, hole_name=hole_name, budget=max(0.0, budget - (monotonic() - started))
                )
            )
        except UnsupportedSynthesisGoal as exc:
            raise UnsupportedSynthesisGoal(
                f"{function.name} needs usable @example/CSV rows, a property equality, or an output refinement: {exc}"
            ) from exc
    return result
