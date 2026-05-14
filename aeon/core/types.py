"""Type hierarchy. Re-exports the Rust core (aeon_rs) plus Python-side
helpers and module-level constants that stay in Python.
"""

from __future__ import annotations

from aeon_rs import AbstractionType as AbstractionType
from aeon_rs import BaseKind as BaseKind
from aeon_rs import Kind as Kind
from aeon_rs import LiquidHornApplication as LiquidHornApplication
from aeon_rs import RefinedType as RefinedType
from aeon_rs import RefinementPolymorphism as RefinementPolymorphism
from aeon_rs import StarKind as StarKind
from aeon_rs import Top as Top
from aeon_rs import Type as Type
from aeon_rs import TypeConstructor as TypeConstructor
from aeon_rs import TypePolymorphism as TypePolymorphism
from aeon_rs import TypeVar as TypeVar

from aeon.core.liquid import (
    LiquidHole,
    LiquidLiteralBool,
    LiquidTerm,
    liquid_free_vars,
)
from aeon.utils.name import fresh_counter, Name

# Default type constructors
t_unit = TypeConstructor(Name("Unit", 0), [])
t_bool = TypeConstructor(Name("Bool", 0), [])
t_int = TypeConstructor(Name("Int", 0), [])
t_float = TypeConstructor(Name("Float", 0), [])
t_string = TypeConstructor(Name("String", 0), [])
t_set = TypeConstructor(Name("Set", 0), [])
t_tensor = TypeConstructor(Name("Tensor", 0), [])
t_gpu_config = TypeConstructor(Name("GpuConfig", 0), [])

builtin_core_types = [t_unit, t_bool, t_int, t_float, t_string, t_set, t_tensor, t_gpu_config]

top = Top()

liq_true = LiquidLiteralBool(True)


def extract_parts(t: Type) -> tuple[Name, "TypeConstructor | TypeVar", LiquidTerm]:
    assert isinstance(t, TypeConstructor) or isinstance(t, RefinedType) or isinstance(t, TypeVar)
    match t:
        case RefinedType(name, ity, ref):
            return (name, ity, ref)
        case _:
            return (Name("_", fresh_counter.fresh()), t, liq_true)


def is_bare(t: Type) -> bool:
    """Returns whether the type is bare."""
    match t:
        case TypeConstructor(_, _) | Top() | TypeVar():
            return True
        case RefinedType(_, _, ref):
            return ref == LiquidHole() or isinstance(ref, LiquidHornApplication)
        case AbstractionType(_, _, vtype):
            return is_bare(vtype) and is_bare(vtype)
        case TypePolymorphism(_, _, ty):
            return is_bare(ty)
        case _:
            assert False, f"Unknown type {t} ({type(t)})"


def base(ty: Type) -> Type:
    """Returns the base type of a Refined Type."""
    if isinstance(ty, RefinedType):
        return ty.type
    return ty


def type_free_term_vars(t: Type) -> list[Name]:
    from aeon.prelude.prelude import ALL_OPS

    if isinstance(t, TypeConstructor):
        return []
    elif isinstance(t, TypeVar):
        return []
    elif isinstance(t, AbstractionType):
        afv = type_free_term_vars(t.var_type)
        rfv = type_free_term_vars(t.type)
        return [x for x in afv + rfv if x != t.var_name and x not in ALL_OPS]
    elif isinstance(t, RefinedType):
        ifv = type_free_term_vars(t.type)
        rfv = liquid_free_vars(t.refinement)
        return [x for x in ifv + rfv if x != t.name]
    elif isinstance(t, TypePolymorphism):
        return type_free_term_vars(t.body)
    return []


def get_type_vars(t: Type) -> set[TypeVar]:
    if isinstance(t, TypeConstructor):
        return set()
    elif isinstance(t, TypeVar):
        return {t}
    elif isinstance(t, AbstractionType):
        return get_type_vars(t.var_type).union(get_type_vars(t.type))
    elif isinstance(t, RefinedType):
        return get_type_vars(t.type)
    elif isinstance(t, TypePolymorphism):
        return {t1 for t1 in get_type_vars(t.body) if t1.name != t.name}
    else:
        assert False, f"Unable to extract {t} ({type(t)})"


def refined_to_unrefined_type(ty: Type) -> Type:
    if isinstance(ty, RefinedType):
        return ty.type
    if isinstance(ty, AbstractionType):
        return AbstractionType(
            ty.var_name,
            refined_to_unrefined_type(ty.var_type),
            refined_to_unrefined_type(ty.type),
        )
    return ty
