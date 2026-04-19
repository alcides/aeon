"""Synquid-style goal decomposition (application spine).

Maps a function type and a goal return type to argument goal types when the
unrefined return shape matches (necessary precondition for APP-style
synthesis). Full round-trip refinement propagation is future work.
"""

from __future__ import annotations

from aeon.core.types import AbstractionType, RefinedType, Type, TypeConstructor, TypePolymorphism, TypeVar
from aeon.core.types import refined_to_unrefined_type


def uncurry(typ: Type) -> tuple[list[Type], Type]:
    match typ:
        case TypeConstructor():
            return [], typ
        case TypeVar(var_name):
            return [], TypeConstructor(var_name, [])
        case AbstractionType(_, _, _):
            t = typ
            params: list[Type] = []
            while isinstance(t, AbstractionType):
                if isinstance(t.var_type, (TypeConstructor, AbstractionType)):
                    params.append(t.var_type)
                else:
                    assert isinstance(t.var_type, RefinedType)
                    if isinstance(t.var_type.type, TypeConstructor):
                        params.append(t.var_type.type)
                if not isinstance(t.type, AbstractionType):
                    break
                t = t.type

            if isinstance(t.type, TypeConstructor):
                return params, t.type
            assert isinstance(t.type, RefinedType)
            return params, t.type.type
        case RefinedType():
            return [], typ.type
        case TypePolymorphism(_, _, body):
            return uncurry(body)
        case _:
            raise AssertionError(f"Unsupported {typ}")


def synquid_application_arg_types(fn_type: Type, goal: Type) -> list[Type] | None:
    """If ``fn_type`` ends in a return compatible with ``goal``'s base, return argument types."""
    try:
        params, ret = uncurry(fn_type)
    except AssertionError:
        return None
    if refined_to_unrefined_type(ret) != refined_to_unrefined_type(refined_to_unrefined_type(goal)):
        return None
    return list(params)
