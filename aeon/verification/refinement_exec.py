"""Compile-time execution of refinement predicates and their closed sub-expressions.

When a refinement ``{v:T | P}`` does not mention its bound variable ``v``, ``P`` is
evaluated using the operational interpreter with the program's definition spine
in scope and replaced by the resulting boolean literal.

When ``P`` *does* mention ``v``, closed sub-expressions that do not mention ``v``
are still evaluated and replaced by literals — e.g.
``{a:Int | a > 1 + 2}`` becomes ``{a:Int | a > 3}``.

Example::

    {a:Int | List.all (fun x => x > 0) [1, 2, 3]}  ==>  {a:Int | true}
    {a:Int | a > 1 + 2}                            ==>  {a:Int | a > 3}
"""

from __future__ import annotations

from aeon.backend.evaluator import EvaluationContext, eval
from aeon.compilation.link import link_rec_spines
from aeon.compilation.unit import CompiledUnit
from aeon.core.terms import Rec, Term
from aeon.prelude.prelude import ALL_OPS, evaluation_vars
from aeon.sugar.ast_helpers import false, st_float, st_int, st_string, true
from aeon.sugar.lowering import lower_to_core, type_to_core
from aeon.sugar.program import (
    SAbstraction,
    SAnnotation,
    SApplication,
    SIf,
    SLet,
    SLiteral,
    SRec,
    SRefinementAbstraction,
    SRefinementApplication,
    STerm,
    STypeAbstraction,
    STypeApplication,
    SVar,
)
from aeon.sugar.stypes import (
    SAbstractionType,
    SRefinedType,
    SRefinementPolymorphism,
    SType,
    STypeConstructor,
    STypePolymorphism,
)
from aeon.utils.name import Name


def sterm_free_vars(term: STerm, *, bound: frozenset[Name] = frozenset()) -> set[Name]:
    """Free value variables in a surface term (ignores type-level binders)."""
    match term:
        case SVar(name):
            if name in bound or name.name in ALL_OPS:
                return set()
            return {name}
        case SLiteral():
            return set()
        case SApplication(fun, arg):
            return sterm_free_vars(fun, bound=bound) | sterm_free_vars(arg, bound=bound)
        case SAbstraction(var_name, body):
            return sterm_free_vars(body, bound=bound | {var_name})
        case SLet(var_name, var_value, body):
            return sterm_free_vars(var_value, bound=bound) | sterm_free_vars(body, bound=bound | {var_name})
        case SRec(var_name, _, var_value, body, _, _, _, _, _):
            inner = bound | {var_name}
            return sterm_free_vars(var_value, bound=inner) | sterm_free_vars(body, bound=inner)
        case SIf(cond, then, otherwise):
            return (
                sterm_free_vars(cond, bound=bound)
                | sterm_free_vars(then, bound=bound)
                | sterm_free_vars(otherwise, bound=bound)
            )
        case SAnnotation(expr, _):
            return sterm_free_vars(expr, bound=bound)
        case STypeApplication(expr, _):
            return sterm_free_vars(expr, bound=bound)
        case STypeAbstraction(name, _, body):
            return sterm_free_vars(body, bound=bound)
        case SRefinementApplication(body, _):
            return sterm_free_vars(body, bound=bound)
        case SRefinementAbstraction(name, _, body):
            return sterm_free_vars(body, bound=bound | {name})
        case _:
            return set()


def _mentions_binder(ref: STerm, binder: Name) -> bool:
    return any(v.name == binder.name for v in sterm_free_vars(ref))


def _bool_literal(value: bool) -> SLiteral:
    return true if value else false


def _sterm_from_runtime_value(value: object) -> STerm | None:
    if isinstance(value, bool):
        return _bool_literal(value)
    if isinstance(value, int):
        return SLiteral(value, st_int)
    if isinstance(value, float):
        return SLiteral(value, st_float)
    if isinstance(value, str):
        return SLiteral(value, st_string)
    return None


def _try_execute_subexpr(
    term: STerm,
    binder: Name,
    program_sterm: STerm,
    dependency_units: list[CompiledUnit],
) -> STerm | None:
    if _mentions_binder(term, binder):
        return None
    try:
        ref_core = lower_to_core(term)
        linked = _eval_context_for_refinement(ref_core, program_sterm, dependency_units)
        result = eval(linked, EvaluationContext(evaluation_vars))
    except Exception:
        return None
    return _sterm_from_runtime_value(result)


def _reduce_closed_subexprs(
    term: STerm,
    binder: Name,
    program_sterm: STerm,
    dependency_units: list[CompiledUnit],
) -> STerm:
    reduced: STerm
    match term:
        case SApplication(fun, arg, loc):
            reduced = SApplication(
                _reduce_closed_subexprs(fun, binder, program_sterm, dependency_units),
                _reduce_closed_subexprs(arg, binder, program_sterm, dependency_units),
                loc=loc,
            )
        case SAbstraction(var_name, body, loc):
            reduced = SAbstraction(
                var_name,
                _reduce_closed_subexprs(body, binder, program_sterm, dependency_units),
                loc=loc,
            )
        case SIf(cond, then, otherwise, loc):
            reduced = SIf(
                _reduce_closed_subexprs(cond, binder, program_sterm, dependency_units),
                _reduce_closed_subexprs(then, binder, program_sterm, dependency_units),
                _reduce_closed_subexprs(otherwise, binder, program_sterm, dependency_units),
                loc=loc,
            )
        case SAnnotation(expr, ty, loc):
            reduced = SAnnotation(
                _reduce_closed_subexprs(expr, binder, program_sterm, dependency_units),
                ty,
                loc=loc,
            )
        case STypeApplication(expr, ty, loc):
            reduced = STypeApplication(
                _reduce_closed_subexprs(expr, binder, program_sterm, dependency_units),
                ty,
                loc=loc,
            )
        case SRefinementApplication(body, refinement, loc):
            reduced = SRefinementApplication(
                _reduce_closed_subexprs(body, binder, program_sterm, dependency_units),
                _reduce_closed_subexprs(refinement, binder, program_sterm, dependency_units),
                loc=loc,
            )
        case SLet() | SRec():
            return term
        case _:
            reduced = term

    executed = _try_execute_subexpr(reduced, binder, program_sterm, dependency_units)
    return executed if executed is not None else reduced


def _execute_refinement(
    ref: STerm,
    binder: Name,
    program_sterm: STerm,
    dependency_units: list[CompiledUnit],
) -> STerm:
    full = try_execute_refinement(ref, binder, program_sterm, dependency_units)
    if full is not None:
        return full
    return _reduce_closed_subexprs(ref, binder, program_sterm, dependency_units)


def _lower_spine_with_body(sterm: STerm, body: Term) -> Term:
    """Lower an ``SRec`` chain, replacing its final body with ``body``."""
    match sterm:
        case SRec(var_name, var_type, var_value, rest, decreasing_by, loc, multiplicity, mutual_group_id, _companions):
            return Rec(
                var_name,
                type_to_core(var_type),
                lower_to_core(var_value),
                _lower_spine_with_body(rest, body),
                decreasing_by=tuple(lower_to_core(m) for m in decreasing_by),
                loc=loc,
                multiplicity=multiplicity,
                mutual_group_id=mutual_group_id,
            )
        case _:
            return body


def _eval_context_for_refinement(
    ref_core: Term,
    program_sterm: STerm,
    dependency_units: list[CompiledUnit],
) -> Term:
    if isinstance(program_sterm, SRec):
        return _lower_spine_with_body(program_sterm, ref_core)
    if dependency_units:
        return link_rec_spines(dependency_units, ref_core)
    return ref_core


def try_execute_refinement(
    ref: STerm,
    binder: Name,
    program_sterm: STerm,
    dependency_units: list[CompiledUnit],
) -> STerm | None:
    """Evaluate a closed refinement predicate; ``None`` if not executable."""
    if _mentions_binder(ref, binder):
        return None
    try:
        ref_core = lower_to_core(ref)
        linked = _eval_context_for_refinement(ref_core, program_sterm, dependency_units)
        result = eval(linked, EvaluationContext(evaluation_vars))
    except Exception:
        return None
    if isinstance(result, bool):
        return _bool_literal(result)
    return None


def execute_refinements_in_stype(
    ty: SType,
    program_sterm: STerm,
    dependency_units: list[CompiledUnit],
) -> SType:
    match ty:
        case SRefinedType(name, base, ref, loc):
            new_ref = _execute_refinement(ref, name, program_sterm, dependency_units)
            return SRefinedType(
                name,
                execute_refinements_in_stype(base, program_sterm, dependency_units),
                new_ref,
                loc=loc,
            )
        case SAbstractionType(var_name, var_type, body, loc, multiplicity, is_instance):
            return SAbstractionType(
                var_name,
                execute_refinements_in_stype(var_type, program_sterm, dependency_units),
                execute_refinements_in_stype(body, program_sterm, dependency_units),
                loc=loc,
                multiplicity=multiplicity,
                is_instance=is_instance,
            )
        case STypePolymorphism(name, kind, body, loc):
            return STypePolymorphism(
                name, kind, execute_refinements_in_stype(body, program_sterm, dependency_units), loc=loc
            )
        case SRefinementPolymorphism(name, sort, body, loc):
            return SRefinementPolymorphism(
                name,
                execute_refinements_in_stype(sort, program_sterm, dependency_units),
                execute_refinements_in_stype(body, program_sterm, dependency_units),
                loc=loc,
            )
        case STypeConstructor(name, args, loc):
            return STypeConstructor(
                name,
                [execute_refinements_in_stype(a, program_sterm, dependency_units) for a in args],
                loc=loc,
            )
        case _:
            return ty


def execute_refinements_in_sterm(
    term: STerm,
    dependency_units: list[CompiledUnit],
) -> STerm:
    return _execute_refinements_in_sterm(term, term, dependency_units)


def _execute_refinements_in_sterm(
    term: STerm,
    program_sterm: STerm,
    dependency_units: list[CompiledUnit],
) -> STerm:
    match term:
        case SRec(var_name, var_type, var_value, body, decreasing_by, loc, multiplicity, mutual_group_id, companions):
            return SRec(
                var_name,
                execute_refinements_in_stype(var_type, program_sterm, dependency_units),
                _execute_refinements_in_sterm(var_value, program_sterm, dependency_units),
                _execute_refinements_in_sterm(body, program_sterm, dependency_units),
                decreasing_by=decreasing_by,
                loc=loc,
                multiplicity=multiplicity,
                mutual_group_id=mutual_group_id,
                companions=companions,
            )
        case SLet(var_name, var_value, body, loc, multiplicity):
            return SLet(
                var_name,
                _execute_refinements_in_sterm(var_value, program_sterm, dependency_units),
                _execute_refinements_in_sterm(body, program_sterm, dependency_units),
                loc=loc,
                multiplicity=multiplicity,
            )
        case SAbstraction(var_name, body, loc):
            return SAbstraction(
                var_name,
                _execute_refinements_in_sterm(body, program_sterm, dependency_units),
                loc=loc,
            )
        case SAnnotation(expr, ty, loc):
            return SAnnotation(
                _execute_refinements_in_sterm(expr, program_sterm, dependency_units),
                execute_refinements_in_stype(ty, program_sterm, dependency_units),
                loc=loc,
            )
        case SApplication(fun, arg, loc):
            return SApplication(
                _execute_refinements_in_sterm(fun, program_sterm, dependency_units),
                _execute_refinements_in_sterm(arg, program_sterm, dependency_units),
                loc=loc,
            )
        case SIf(cond, then, otherwise, loc):
            return SIf(
                _execute_refinements_in_sterm(cond, program_sterm, dependency_units),
                _execute_refinements_in_sterm(then, program_sterm, dependency_units),
                _execute_refinements_in_sterm(otherwise, program_sterm, dependency_units),
                loc=loc,
            )
        case STypeApplication(expr, ty, loc):
            return STypeApplication(
                _execute_refinements_in_sterm(expr, program_sterm, dependency_units),
                execute_refinements_in_stype(ty, program_sterm, dependency_units),
                loc=loc,
            )
        case SRefinementApplication(body, refinement, loc):
            return SRefinementApplication(
                _execute_refinements_in_sterm(body, program_sterm, dependency_units),
                _execute_refinements_in_sterm(refinement, program_sterm, dependency_units),
                loc=loc,
            )
        case _:
            return term
