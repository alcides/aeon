from __future__ import annotations

from typing import Callable

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidTerm, LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.terms import Abstraction, Application, If, Literal, Term, Var
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    Type,
    TypeConstructor,
    TypePolymorphism,
    RefinementPolymorphism,
    t_bool,
    t_float,
    t_int,
)
from aeon.synthesis.modules.tdsyn.helpers import (
    base_type_of,
    bases_match,
    get_param_types,
    get_return_type,
    is_subtype,
    monomorphize,
)
from aeon.synthesis.modules.tdsyn.worklist import TypedHole, fresh_hole
from aeon.typechecking.context import TypingContext
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name

_loc = SynthesizedLocation("tdsyn")


def get_applicable_functions(
    ctx: TypingContext,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, Type]]:
    """Get all applicable functions from context, monomorphizing polymorphic ones.

    Returns list of (term, monomorphic_function_type) pairs where term is
    Var(f) for monomorphic functions or TypeApplication(Var(f), T) for
    instantiated polymorphic ones.
    """
    results: list[tuple[Term, Type]] = []
    for name, ty in ctx.vars():
        if skip(name):
            continue
        if isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
            for term, mono_ty in monomorphize(name, ty, ctx):
                if isinstance(mono_ty, AbstractionType):
                    results.append((term, mono_ty))
        elif isinstance(ty, AbstractionType):
            results.append((Var(name, _loc), ty))
    return results


def _extract_refinement(ty: Type) -> tuple[Name, LiquidTerm] | None:
    """Extract (binder_name, refinement) from a refined type, or None."""
    match ty:
        case RefinedType(binder, _, refinement):
            if refinement != LiquidLiteralBool(True):
                return (binder, refinement)
        case _:
            pass
    return None


def _build_liquid_app(fun_name: Name, hole_names: list[Name]) -> LiquidTerm:
    """Build a liquid application term: f(h1, h2, ..., hn) for constraint propagation."""
    if len(hole_names) == 0:
        return LiquidVar(fun_name)
    return LiquidApp(fun_name, [LiquidVar(h) for h in hole_names])


def _propagate_constraints(
    hole: TypedHole,
    fun_name: Name,
    new_holes: list[TypedHole],
) -> None:
    """Propagate refinement constraints from parent hole to parameter holes.

    If the parent hole expects {x:T | R(x)} and we're applying f(h1, h2, ...),
    the constraint R(f(h1, h2, ...)) is added to all parameter holes.
    """
    ref_info = _extract_refinement(hole.expected_type)
    if ref_info is None:
        # Also propagate any existing constraints from parent hole
        if hole.constraints:
            for h in new_holes:
                h.constraints.extend(hole.constraints)
        return

    binder, refinement = ref_info
    # Build liquid expression: f(h1, h2, ...)
    hole_names = [h.name for h in new_holes]
    liquid_expr = _build_liquid_app(fun_name, hole_names)

    # Substitute: R(x) becomes R(f(h1, h2, ...))
    propagated = substitution_in_liquid(refinement, liquid_expr, binder)

    # Attach constraint to all parameter holes
    for h in new_holes:
        h.constraints.append(propagated)
        # Also propagate parent's accumulated constraints
        h.constraints.extend(hole.constraints)


def _get_operator_name(f_term: Term) -> Name | None:
    """Extract the function name from a term (Var or TypeApplication(Var, ...))."""
    match f_term:
        case Var(name, _):
            return name
        case _:
            # For TypeApplication(Var(name), type), walk down
            t = f_term
            from aeon.core.terms import TypeApplication as TA

            while isinstance(t, TA):
                t = t.body
            if isinstance(t, Var):
                return t.name
            return None


def _build_application(
    f_term: Term,
    param_types: list[tuple[Name, Type]],
    hole: TypedHole,
) -> tuple[Term, list[TypedHole]]:
    """Build a curried application f(h1)(h2)...(hn) with fresh holes for each parameter.

    Propagates refinement constraints from the parent hole to parameter holes.
    """
    new_holes: list[TypedHole] = []
    result = f_term
    for _, param_type in param_types:
        hole_term, typed_hole = fresh_hole(param_type, hole.context)
        result = Application(result, hole_term, _loc)
        new_holes.append(typed_hole)

    # Propagate constraints
    fun_name = _get_operator_name(f_term)
    if fun_name is not None:
        _propagate_constraints(hole, fun_name, new_holes)

    return result, new_holes


def backward_candidates(
    hole: TypedHole,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, list[TypedHole]]]:
    """Backward action: from expected type, find terms that produce a subtype.

    Given hole expecting type T:
    1. If T is a function type, produce an abstraction
    2. Generate literals for base types
    3. Look up variables with matching types
    4. Find functions whose return type matches T
    5. Generate if-then-else
    """
    T = hole.expected_type
    ctx = hole.context
    candidates: list[tuple[Term, list[TypedHole]]] = []

    # 1. Abstraction for function types
    match T:
        case AbstractionType(var_name, var_type, body_type):
            body_hole_term, body_typed_hole = fresh_hole(body_type, ctx.with_var(var_name, var_type))
            candidates.append((Abstraction(var_name, body_hole_term, _loc), [body_typed_hole]))
            return candidates  # For function types, only produce abstractions
        case _:
            pass

    # 2. Literals
    base = base_type_of(T)
    if base is not None:
        match base:
            case TypeConstructor(Name("Int", _)):
                for ival in range(-2, 11):
                    candidates.append((Literal(ival, t_int, _loc), []))
            case TypeConstructor(Name("Bool", _)):
                candidates.append((Literal(True, t_bool, _loc), []))
                candidates.append((Literal(False, t_bool, _loc), []))
            case TypeConstructor(Name("Float", _)):
                for fval in [-1.0, -0.5, 0.0, 0.5, 1.0, 2.0]:
                    candidates.append((Literal(fval, t_float, _loc), []))
            case _:
                pass

    # 3. Variables (non-function types)
    for name, var_type in ctx.vars():
        if skip(name):
            continue
        if isinstance(var_type, (AbstractionType, TypePolymorphism, RefinementPolymorphism)):
            continue
        if bases_match(var_type, T):
            if is_subtype(ctx, var_type, T):
                candidates.append((Var(name, _loc), []))

    # 4. Function applications (monomorphic + polymorphic)
    for f_term, f_type in get_applicable_functions(ctx, skip):
        assert isinstance(f_type, AbstractionType)
        ret_type = get_return_type(f_type)
        if bases_match(ret_type, T):
            params = get_param_types(f_type)
            app_term, new_holes = _build_application(f_term, params, hole)
            candidates.append((app_term, new_holes))

    # 5. If-then-else
    cond_hole_term, cond_typed_hole = fresh_hole(t_bool, ctx)
    then_hole_term, then_typed_hole = fresh_hole(T, ctx)
    else_hole_term, else_typed_hole = fresh_hole(T, ctx)
    candidates.append(
        (
            If(cond_hole_term, then_hole_term, else_hole_term, _loc),
            [cond_typed_hole, then_typed_hole, else_typed_hole],
        )
    )

    return candidates


def forward_candidates(
    hole: TypedHole,
    skip: Callable[[Name], bool],
) -> list[tuple[Term, list[TypedHole]]]:
    """Forward action: from variables in scope, find functions that consume them.

    Given hole expecting type T, for each variable v:A in scope, find functions
    f:(x:A)->B where A is compatible with v's type, and produce f(v) with
    remaining holes if needed.
    """
    T = hole.expected_type
    ctx = hole.context
    candidates: list[tuple[Term, list[TypedHole]]] = []

    # Collect concrete (non-function) variables
    concrete_vars: list[tuple[Name, Type]] = []
    for name, var_type in ctx.vars():
        if skip(name):
            continue
        if isinstance(var_type, (AbstractionType, TypePolymorphism, RefinementPolymorphism)):
            continue
        concrete_vars.append((name, var_type))

    # For each variable, find functions that accept it
    for v_name, v_type in concrete_vars:
        for f_term, f_type in get_applicable_functions(ctx, skip):
            assert isinstance(f_type, AbstractionType)
            first_param_type = f_type.var_type

            if not bases_match(v_type, first_param_type):
                continue
            if not is_subtype(ctx, v_type, first_param_type):
                continue

            # Apply f to v
            applied = Application(f_term, Var(v_name, _loc), _loc)
            remaining_type = f_type.type

            if isinstance(remaining_type, AbstractionType):
                # Multi-argument function: create holes for remaining args
                remaining_params = get_param_types(remaining_type)
                final_ret = get_return_type(remaining_type)
                if not bases_match(final_ret, T):
                    continue
                result, new_holes = _build_application(applied, remaining_params, hole)
                candidates.append((result, new_holes))
            else:
                # Single-argument or final application
                if bases_match(remaining_type, T):
                    candidates.append((applied, []))

    return candidates
