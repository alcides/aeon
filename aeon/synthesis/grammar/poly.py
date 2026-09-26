"""Polymorphism / refinement helpers shared by synthesis backends.

Previously lived in the GeneticEngine grammar builder; kept here so tree-automata
and PBT shrinking can strip uninterpreted refinements and monomorphize foralls
without a GeneticEngine dependency.
"""

from __future__ import annotations

from itertools import product
from typing import Optional

from aeon.core.liquid import (
    LiquidApp,
    LiquidHole,
    LiquidLiteralBool,
    LiquidLiteralFloat,
    LiquidLiteralInt,
    LiquidLiteralString,
    LiquidLiteralUnit,
    LiquidTerm,
    LiquidVar,
)
from aeon.core.liquid_ops import ops
from aeon.core.substitutions import substitute_vartype
from aeon.core.types import (
    AbstractionType,
    RefinementPolymorphism,
    RefinedType,
    Top,
    Type,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
    t_bool,
    t_float,
    t_int,
    t_string,
)
from aeon.utils.name import Name

# Base sorts used to instantiate foralls when the program contributes no type
# arguments (plain ``Int``/``Float`` holes).
DEFAULT_POLY_INSTANTIATION_UNIVERSE: frozenset[TypeConstructor] = frozenset({t_int, t_float, t_bool, t_string})


def filter_uninterpreted(lt: LiquidTerm) -> Optional[LiquidTerm]:
    match lt:
        case LiquidHole():
            return lt
        case (
            LiquidLiteralBool(_)
            | LiquidLiteralInt(_)
            | LiquidLiteralFloat(_)
            | LiquidLiteralString(_)
            | LiquidLiteralUnit()
            | LiquidVar(_)
        ):
            return lt
        case LiquidApp(fun, args):
            if fun in ["&&", "||"]:
                nargs = [filter_uninterpreted(x) for x in args]
                if nargs[0] is None:
                    return nargs[1]
                if nargs[1] is None:
                    return nargs[0]
                return LiquidApp(fun, nargs)
            elif fun in ops:
                nargs = [filter_uninterpreted(x) for x in args]
                if None not in nargs:
                    return LiquidApp(fun, nargs)
                else:
                    return None
            else:
                return None
        case _:
            assert False, f"Failed {lt}"


def remove_uninterpreted_functions_from_type(ty: Type) -> Type:
    match ty:
        case TypeConstructor(_, _) | TypeVar(_) | Top():
            return ty
        case AbstractionType(var_name, var_type, type):
            return AbstractionType(
                var_name,
                remove_uninterpreted_functions_from_type(var_type),
                remove_uninterpreted_functions_from_type(type),
            )
        case RefinedType(name, type, ref):
            ref_filtered = filter_uninterpreted(ref)
            if ref_filtered is None:
                return type
            else:
                return RefinedType(name, type, ref_filtered)
        case TypePolymorphism(name, kind, body):
            return TypePolymorphism(name, kind, remove_uninterpreted_functions_from_type(body))
        case RefinementPolymorphism(name, sort, body):
            # Keep the abstract-refinement binder; callers that need a bare
            # function type peel it themselves (or open it with an
            # ImplicitRefinementHole via monomorphize).
            return RefinementPolymorphism(
                name,
                remove_uninterpreted_functions_from_type(sort),
                remove_uninterpreted_functions_from_type(body),
            )
        case _:
            assert False, f"Unsupported {ty}"


def monomorphize_poly_type(
    ty: TypePolymorphism,
    instantiation_types: set[TypeConstructor],
    program_types: set[TypeConstructor] | None = None,
) -> list[tuple[Type, list[Type]]]:
    """Monomorphize a polymorphic type by instantiating forall-bound vars.

    Returns list of (monomorphized_body, type_applications) pairs.
    """
    foralls: list[Name] = []
    current: Type = ty
    while isinstance(current, TypePolymorphism):
        foralls.append(current.name)
        current = current.body

    if isinstance(current, RefinementPolymorphism):
        return []

    base_types = sorted(instantiation_types, key=repr)
    if not base_types:
        return []

    if len(foralls) <= 1 or program_types is None:
        combos: list[tuple[TypeConstructor, ...]] = list(product(base_types, repeat=len(foralls)))
    else:
        combo_set: set[tuple[TypeConstructor, ...]] = set()
        prog = sorted(program_types, key=repr)
        if prog:
            combo_set.update(product(prog, repeat=len(foralls)))
        for t in base_types:
            combo_set.add(tuple([t] * len(foralls)))
        combos = sorted(combo_set, key=repr)

    results = []
    for combo in combos:
        body = current
        type_apps: list[Type] = list(combo)
        for tvar_name, concrete_ty in zip(foralls, combo):
            body = substitute_vartype(body, concrete_ty, tvar_name)
        results.append((body, type_apps))

    return results
