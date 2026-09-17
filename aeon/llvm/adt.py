"""Tagged-heap layouts for immutable inductive types in the CPU LLVM backend.

Nullary constructors that are the sole zero-argument ctor of a type are
represented as a null pointer. All other values are heap nodes:

    [i32 tag][i32 pad][i64 field0][i64 field1]...

Integers occupy the low 32 bits of a field slot; nested ADT values are
pointers bitcast to i64. Constructors and ``Type_rec`` eliminators are
recognized by name via the desugar constructor registry.
"""

from __future__ import annotations

from dataclasses import dataclass

from aeon.core.types import Type, TypeConstructor, RefinedType, TypeVar
from aeon.llvm.llvm_ast import (
    LLVMType,
    LLVMInt,
    LLVMBool,
    LLVMFloat,
    LLVMDouble,
    LLVMPointerType,
    LLVMCharType,
)
from aeon.verification.constructor_registry import (
    get_constructor_groups,
    get_constructor_order,
    get_constructor_fields,
    get_type_param_count,
)


# Opaque ADT handle used everywhere inductives appear in LLVM.
LLVMADTPtr = LLVMPointerType(LLVMCharType())
ADT_PTR_BITS = 64


@dataclass(frozen=True)
class ADTConstructorInfo:
    type_name: str
    ctor_name: str  # prefixed, e.g. Individual_gene
    tag: int
    arity: int
    nullary_as_null: bool


def _strip_id_suffix(name: str) -> str:
    parts = name.rsplit("_", 1)
    if len(parts) == 2 and parts[1].isdigit():
        return parts[0]
    return name


def lookup_constructor(name: str) -> ADTConstructorInfo | None:
    """Resolve a (possibly id-suffixed) constructor name to layout info."""
    bare = _strip_id_suffix(name)
    for type_name, ctors in get_constructor_groups().items():
        order = get_constructor_order(type_name) or sorted(ctors)
        if bare not in order:
            continue
        tag = order.index(bare)
        return ADTConstructorInfo(type_name, bare, tag, arity=-1, nullary_as_null=False)
    return None


def finalize_constructor(info: ADTConstructorInfo, arity: int) -> ADTConstructorInfo:
    # Null-encode only the tag-0 nullary constructor (nil / empty_*).
    nullary_as_null = arity == 0 and info.tag == 0
    return ADTConstructorInfo(info.type_name, info.ctor_name, info.tag, arity, nullary_as_null)


def lookup_recursor(name: str) -> str | None:
    """If ``name`` is ``Type_rec``, return ``Type``; else None."""
    bare = _strip_id_suffix(name)
    if not bare.endswith("_rec"):
        return None
    type_name = bare[: -len("_rec")]
    if type_name in get_constructor_groups():
        return type_name
    return None


def is_registered_inductive(type_name: str) -> bool:
    return type_name in get_constructor_groups()


def constructor_order(type_name: str) -> list[str]:
    return get_constructor_order(type_name) or sorted(get_constructor_groups().get(type_name, []))


def type_param_count(type_name: str) -> int:
    return get_type_param_count(type_name)


def _unwrap_type(ty: Type) -> Type:
    while isinstance(ty, RefinedType):
        ty = ty.type
    return ty


def core_type_to_llvm(ty: Type) -> LLVMType:
    ty = _unwrap_type(ty)
    match ty:
        case TypeConstructor(n, _) if n.name == "Int":
            return LLVMInt
        case TypeConstructor(n, _) if n.name == "Bool":
            return LLVMBool
        case TypeConstructor(n, _) if n.name == "Float":
            return LLVMFloat
        case TypeConstructor(n, _) if n.name == "Double":
            return LLVMDouble
        case TypeConstructor(n, _) if is_registered_inductive(n.name):
            return LLVMADTPtr
        case TypeVar(_):
            return LLVMInt
        case _:
            return LLVMInt


def resolve_field_llvm_types(ctor_name: str, type_args: list[Type]) -> list[LLVMType]:
    """Map a constructor's field skeletons to LLVM types under ``type_args``."""
    skeletons = get_constructor_fields(ctor_name)
    if skeletons is None:
        return []
    out: list[LLVMType] = []
    for skel in skeletons:
        if skel.startswith("#"):
            idx = int(skel[1:])
            if idx < len(type_args):
                out.append(core_type_to_llvm(type_args[idx]))
            else:
                out.append(LLVMInt)
        elif is_registered_inductive(skel):
            out.append(LLVMADTPtr)
        elif skel == "Int":
            out.append(LLVMInt)
        elif skel == "Bool":
            out.append(LLVMBool)
        elif skel == "Float":
            out.append(LLVMFloat)
        elif skel == "Double":
            out.append(LLVMDouble)
        else:
            # Unknown / polymorphic leftover → opaque ADT or int.
            out.append(LLVMADTPtr if is_registered_inductive(skel) else LLVMInt)
    return out
