from abc import ABC
from dataclasses import dataclass
from functools import reduce

from aeon.core.types import Kind

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from aeon.sugar.program import STerm


class SType(ABC):
    "Surface-level Type Representation"
    pass


@dataclass(unsafe_hash=True)
class STypeVar(SType):
    name: str


@dataclass(unsafe_hash=True)
class SBaseType(SType):
    name: str


@dataclass(unsafe_hash=True)
class SRefinedType(SType):
    name: str
    type: SType
    refinement: "STerm"


@dataclass(unsafe_hash=True)
class SAbstractionType(SType):
    var_name: str
    var_type: SType
    type: SType


@dataclass(unsafe_hash=True)
class STypePolymorphism(SType):
    name: str
    kind: Kind
    body: SType


@dataclass
class STypeConstructor(SType):
    name: str
    args: list[SType]

    def __str__(self):
        args = ", ".join(str(a) for a in self.args)
        return f"{self.name} {args}"

    def __hash__(self):
        return hash(self.name) + sum(hash(c) for c in self.args)


builtin_types = ["Top", "Bool", "Int", "Float", "String", "Unit"]


def get_type_vars(ty: SType) -> set[STypeVar]:
    match ty:
        case SBaseType(name):
            return set()
        case STypeVar(name):
            return {ty}
        case SAbstractionType(_, vtype, rtype):
            return get_type_vars(vtype).union(get_type_vars(rtype))
        case SRefinedType(_, rty, _):
            return get_type_vars(rty)
        case STypePolymorphism(name, _, body):
            return {t1 for t1 in get_type_vars(body) if t1.name != name}
        case STypeConstructor(name, args):
            return reduce(lambda acc, v: acc.union(get_type_vars(v)), args,
                          set())
        case _:
            assert False, f"Unknown type ({ty}) ({type(ty)})"
