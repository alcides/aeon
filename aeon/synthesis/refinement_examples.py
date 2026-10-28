"""Bounded, checked I/O samples derived from a function's refinement.

The normal SMT translation supplies the relation. Constructor contracts tie
ADT measures to real payloads; models of uninterpreted measures alone are not
executable examples. Non-unique outputs remain relational observations rather
than being silently promoted to exact labels (for example, a circuit's depth
must remain free when only its logical outputs are specified).
"""

from __future__ import annotations

import os
from time import monotonic
from typing import Any

import z3

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.substitutions import substitute_vartype, substitution_in_type
from aeon.core.terms import Abstraction, Annotation, Application, Hole, Let, Literal, Rec, Term, TypeApplication, Var
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    Type,
    TypeConstructor,
    TypePolymorphism,
    t_bool,
    t_float,
    t_int,
    t_string,
)
from aeon.synthesis.api import SynthesisNotSuccessful, UnsupportedSynthesisGoal
from aeon.typechecking.context import TypingContext
from aeon.typechecking.entailment import entailment_context
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name, fresh_counter
from aeon.verification.constructor_registry import get_constructor_order
from aeon.verification.smt import (
    base_functions,
    flatten,
    get_sort,
    make_variable,
    mk_funs,
    mk_sorts,
    translate,
    translate_liq,
)
from aeon.verification.smt_datatypes import constructors_for_env, measures_for_env
from aeon.verification.vcs import LiquidConstraint


def _base(ty: Type) -> TypeConstructor:
    ty = ty.type if isinstance(ty, RefinedType) else ty
    if not isinstance(ty, TypeConstructor):
        raise UnsupportedSynthesisGoal(f"Cannot derive examples for type {ty}")
    return ty


def _constructor(ty: Type, arguments: list[Type]) -> Type:
    for argument in arguments:
        if not isinstance(ty, TypePolymorphism):
            raise UnsupportedSynthesisGoal("Constructor type parameter mismatch while generating examples")
        ty = substitute_vartype(ty.body, argument, ty.name)
    return ty


def _domain(
    value: Any, ty: Type, constructors: dict[str, tuple[Name, Type]], env: dict, depth: int = 4, *, bounded: bool = True
) -> Any:
    """Constrain a sampled ADT using its declared constructor/field contracts."""
    conditions = []
    if isinstance(ty, RefinedType):
        conditions.append(translate_liq(ty.refinement, env | {str(ty.name): value}))
    base = _base(ty)
    order = get_constructor_order(base.name.name)
    if order is None:
        if base not in (t_int, t_float, t_bool, t_string):
            raise UnsupportedSynthesisGoal(f"Cannot sample opaque type {base}")
        return z3.And(*conditions)
    if depth <= 0:
        return z3.BoolVal(False) if bounded else z3.And(*conditions)
    sort = get_sort(base)
    assert isinstance(sort, z3.DatatypeSortRef)
    for index, tag in enumerate(order):
        current = _constructor(constructors[tag][1], base.args)
        fields = []
        local = dict(env)
        field_index = 0
        while isinstance(current, AbstractionType):
            field = sort.accessor(index, field_index)(value)
            fields.append(_domain(field, current.var_type, constructors, local, depth - 1, bounded=bounded))
            local[str(current.var_name)] = field
            field_index += 1
            current = current.type
        if isinstance(current, RefinedType):
            fields.append(translate_liq(current.refinement, local | {str(current.name): value}))
        conditions.append(z3.Implies(sort.recognizer(index)(value), z3.And(*fields)))
    return z3.And(*conditions)


def _decode(
    value: Any, ty: Type, model: z3.ModelRef, constructors: dict[str, tuple[Name, Type]], depth: int = 4
) -> Any:
    base = _base(ty)
    if base == t_int:
        return value.as_long()
    if base == t_bool:
        return z3.is_true(value)
    if base == t_float:
        if not z3.is_rational_value(value):
            raise UnsupportedSynthesisGoal("Cannot decode a non-rational Float example")
        return value.numerator_as_long() / value.denominator_as_long()
    if base == t_string:
        length = model.eval(z3.Length(value)).as_long()
        if length > 256:
            raise UnsupportedSynthesisGoal("Generated string exceeds the 256-character example limit")
        return "".join(chr(model.eval(z3.StrToCode(z3.SubString(value, i, 1))).as_long()) for i in range(length))
    order = get_constructor_order(base.name.name)
    sort = get_sort(base)
    if not order or not isinstance(sort, z3.DatatypeSortRef) or depth <= 0:
        raise UnsupportedSynthesisGoal(f"Cannot decode a bounded example of {base}")
    index = next(i for i in range(sort.num_constructors()) if value.decl() == sort.constructor(i))
    tag = order[index]
    current = _constructor(constructors[tag][1], base.args)
    fields = []
    for child in value.children():
        if not isinstance(current, AbstractionType):
            raise ValueError("Constructor model has the wrong arity")
        field = _decode(child, current.var_type, model, constructors, depth - 1)
        fields.append(field)
        current = substitution_in_type(
            current.type, _value_term(field, current.var_type, constructors), current.var_name
        )
    return (tag, *fields)


def _value_term(value: Any, ty: Type, constructors: dict[str, tuple[Name, Type]]) -> Term:
    base = _base(ty)
    expected = {t_int: int, t_float: float, t_bool: bool, t_string: str}
    if base in expected:
        if type(value) is not expected[base]:
            raise ValueError(f"Example {value!r} does not have type {base}")
        return Literal(value, base)
    order = get_constructor_order(base.name.name) or []
    if not isinstance(value, tuple) or not value or value[0] not in order:
        raise ValueError(f"Invalid constructor example {value!r}")
    name, signature = constructors[value[0]]
    term: Term = Var(name)
    for argument in base.args:
        term = TypeApplication(term, argument)
    current = _constructor(signature, base.args)
    for field in value[1:]:
        if not isinstance(current, AbstractionType):
            raise ValueError("Too many constructor fields")
        argument_term = _value_term(field, current.var_type, constructors)
        term = Application(term, argument_term)
        current = substitution_in_type(current.type, argument_term, current.var_name)
    if isinstance(current, AbstractionType):
        raise ValueError("Missing constructor fields")
    return term


def _encode(value: Any, ty: Type, constructors: dict[str, tuple[Name, Type]]) -> Any:
    """Encode the decoded value, including any Float rounding, back into SMT."""
    base = _base(ty)
    scalar = {t_int: z3.IntVal, t_float: z3.RealVal, t_bool: z3.BoolVal, t_string: z3.StringVal}
    if base in scalar:
        return scalar[base](value)
    order = get_constructor_order(base.name.name) or []
    index = order.index(value[0])
    sort = get_sort(base)
    assert isinstance(sort, z3.DatatypeSortRef)
    current = _constructor(constructors[value[0]][1], base.args)
    fields = []
    for field in value[1:]:
        assert isinstance(current, AbstractionType)
        fields.append(_encode(field, current.var_type, constructors))
        current = current.type
    return sort.constructor(index)(*fields)


def derive_refinement_examples(
    ctx: TypingContext,
    program: Term,
    function: Name,
    *,
    hole_name: Name | None = None,
    max_examples: int = 32,
    budget: float = 2.0,
) -> dict[str, Any]:
    """Generate synthesis-local metadata without evaluating the unfinished body.

    Exact examples are supplied only if the output is unique for every sampled
    input. Otherwise ``refinement_examples`` contains witnesses and
    ``refinement_example_matches`` checks observations against the relation.
    Every proposed ground input/output is checked by Aeon's typechecker.
    """
    started = monotonic()
    constructors: dict[str, tuple[Name, Type]] = {}
    prefix = ctx
    target = program
    while isinstance(target, (Let, Rec)):
        if isinstance(target, Rec):
            constructors[target.var_name.name] = (target.var_name, target.var_type)
        if target.var_name == function:
            break
        if isinstance(target, Rec):
            prefix = prefix.with_var(target.var_name, target.var_type)
        target = target.body
    if not isinstance(target, Rec) or target.var_name != function:
        raise UnsupportedSynthesisGoal("Example generation requires a top-level function")
    params = []
    declared = target.var_type
    body = target.var_value
    # Function contracts and lambda binders have distinct IDs after lowering.
    while isinstance(declared, AbstractionType) and isinstance(body, Abstraction):
        params.append((body.var_name, declared.var_type))
        declared = substitution_in_type(declared.type, Var(body.var_name), declared.var_name)
        body = body.body
    while isinstance(body, (Let, Rec, Annotation)):
        body = body.expr if isinstance(body, Annotation) else body.body
    if not isinstance(body, Hole) or (hole_name is not None and body.name != hole_name):
        raise UnsupportedSynthesisGoal("Automatic examples require a hole in the function's result position")
    if not isinstance(declared, RefinedType) or declared.refinement == LiquidLiteralBool(True):
        raise UnsupportedSynthesisGoal(f"{function.name} needs an output refinement to derive examples")
    result_name = Name("example_result", fresh_counter.fresh())
    sample_ctx = prefix
    for name, ty in params:
        sample_ctx = sample_ctx.with_var(name, ty)
    sample_ctx = sample_ctx.with_var(result_name, declared)
    try:
        clauses = list(flatten(entailment_context(sample_ctx, LiquidConstraint(LiquidLiteralBool(False)))))
        solver = z3.Solver()
        solver.set(random_seed=int(os.environ.get("AEON_SEED", "0")))
        relation = z3.And(*(translate(clause) for clause in clauses))
        solver.add(relation)
        env = dict(base_functions)
        for clause in clauses:
            env.update(mk_funs(clause.functions, mk_sorts(clause.sorts)))
        env.update(constructors_for_env())
        env.update(measures_for_env())
        variables = [make_variable(str(name), _base(ty)) for name, ty in params]
        output = make_variable(str(result_name), _base(declared))
        env.update({str(name): value for (name, _), value in zip(params, variables)})
        for (_, ty), value in zip(params, variables):
            solver.add(_domain(value, ty, constructors, env))
        solver.add(_domain(output, declared, constructors, env))
        uniqueness_solver = z3.Solver()
        uniqueness_solver.set(timeout=200)
        uniqueness_solver.add(relation, _domain(output, declared, constructors, env, bounded=False))
        for (_, ty), value in zip(params, variables):
            uniqueness_solver.add(_domain(value, ty, constructors, env, bounded=False))
        rows: list[tuple[list[Any], Any]] = []
        targets: list[Type] = []
        unique = True
        complete = False
        input_blocks = []
        seen = set()
        for _ in range(max_examples * 4):
            remaining = budget - (monotonic() - started)
            if remaining <= 0 or len(rows) >= max_examples:
                break
            solver.set(timeout=max(1, min(200, int(remaining * 1000))))
            status = solver.check()
            if status != z3.sat:
                complete = status == z3.unsat
                break
            model = solver.model()
            raw_inputs = [model.eval(value, model_completion=True) for value in variables]
            raw_output = model.eval(output, model_completion=True)
            inputs = [_decode(value, ty, model, constructors) for (_, ty), value in zip(params, raw_inputs)]
            expected = _decode(raw_output, declared, model, constructors)
            specialised: Type = declared
            selected: list[tuple[Name, Term]] = []
            valid = True
            for (name, ty), value in zip(params, inputs):
                for previous, argument in selected:
                    ty = substitution_in_type(ty, argument, previous)
                argument = _value_term(value, ty, constructors)
                valid = valid and check_type(prefix, argument, ty)
                selected.append((name, argument))
                specialised = substitution_in_type(specialised, argument, name)
            valid = valid and check_type(prefix, _value_term(expected, declared, constructors), specialised)
            # Block only this concrete model if a decoded witness did not
            # survive checking, allowing a different output for these inputs.
            if not valid:
                solver.add(z3.Or(output != raw_output, *(v != x for v, x in zip(variables, raw_inputs))))
                continue
            encoded_inputs = [_encode(value, ty, constructors) for (_, ty), value in zip(params, inputs)]
            encoded_output = _encode(expected, declared, constructors)
            identity = tuple(value.sexpr() for value in encoded_inputs)
            if identity in seen:
                solver.add(z3.Or(*(v != x for v, x in zip(variables, raw_inputs))))
                continue
            seen.add(identity)
            uniqueness_solver.push()
            uniqueness_solver.add(*(v == x for v, x in zip(variables, encoded_inputs)), output != encoded_output)
            # Use the unbounded relation for uniqueness: a bounded ADT corpus
            # must never make a nonfunctional refinement look functional.
            unique = (uniqueness_solver.check() == z3.unsat) and unique
            uniqueness_solver.pop()
            rows.append((inputs, expected))
            targets.append(specialised)
            input_blocks.append(z3.Or(*(v != x for v, x in zip(variables, encoded_inputs))))
            solver.add(z3.Or(*(v != x for v, x in zip(variables, raw_inputs))))
        if complete:
            uniqueness_solver.add(*input_blocks)
            complete = uniqueness_solver.check() == z3.unsat
    except (AssertionError, KeyError, TypeError, ValueError, z3.Z3Exception) as exc:
        raise UnsupportedSynthesisGoal(f"Cannot derive refinement examples for {function.name}: {exc}") from exc
    if not rows:
        raise SynthesisNotSuccessful(f"No checked refinement examples for {function.name} within the generation budget")

    def matches(outputs: tuple[Any, ...]) -> bool:
        if len(outputs) != len(rows):
            return False
        try:
            return all(
                check_type(prefix, _value_term(out, declared, constructors), ty) for out, ty in zip(outputs, targets)
            )
        except (AssertionError, KeyError, TypeError, ValueError, z3.Z3Exception):
            return False

    entry: dict[str, Any] = {
        "io_params": [name for name, _ in params],
        "refinement_examples": rows,
        "refinement_example_matches": matches,
        "refinement_examples_unique": unique,
        "refinement_examples_complete": complete,
    }
    if unique:
        entry["constructor_io_examples"] = rows
        entry["io_examples"] = rows
        if all(_base(ty) in (t_int, t_float) for _, ty in params) and _base(declared) in (t_int, t_float):
            entry["training_data"] = [[*args, out] for args, out in rows]
    return entry
