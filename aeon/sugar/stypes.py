from abc import ABC
from dataclasses import dataclass, field
from functools import reduce

from aeon.core.types import Kind

from typing import TYPE_CHECKING


from aeon.utils.location import Location, SynthesizedLocation
from aeon.utils.name import Name

if TYPE_CHECKING:
    from aeon.sugar.program import STerm


class SType(ABC):
    "Surface-level Type Representation"

    loc: Location


@dataclass(unsafe_hash=True)
class STypeVar(SType):
    name: Name
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"'{self.name}"


@dataclass(unsafe_hash=True)
class SRefinedType(SType):
    name: Name
    type: SType
    refinement: "STerm"
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"{{{self.name} : {self.type} | {self.refinement} }}"


@dataclass(unsafe_hash=True)
class SAbstractionType(SType):
    var_name: Name
    var_type: SType
    type: SType
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"({self.var_name} : {self.var_type}) -> {self.type}"


@dataclass(unsafe_hash=True)
class STypePolymorphism(SType):
    name: Name
    kind: Kind
    body: SType
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"∀{self.name}:{self.kind}. {self.body}"


@dataclass(unsafe_hash=True)
class SRefinementPolymorphism(SType):
    name: Name
    type: SType
    body: SType
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"∀{self.name}:{self.type}. {self.body}"

    # TODO: Post-initialization to ensure that the body is well-formed
    def __post_init__(self):
        # Ensures type, is a function of basic types, that returns a boolean
        valid = True
        done = False
        curr = self.type
        while valid and not done:
            match curr:
                case STypeVar(_):
                    done = True
                case SAbstractionType(_, vtype, rtype):
                    valid = is_basic_type(vtype)
                    curr = rtype
                case STypeConstructor(name, _):
                    valid = name.name == "Bool"
                    done = True
                case _:
                    valid = False
        assert valid, f"Invalid refinement type {self.type} in {self.name}:{self.type}. {self.body}"


def is_basic_type(ty: SType) -> bool:
    """Check if the type is a basic type (e.g., Int, Bool, Float, String, Unit)"""
    match ty:
        case STypeVar(_):
            return True
        case STypeConstructor(_, _):
            return True
        case _:
            return False


@dataclass
class STypeConstructor(SType):
    name: Name
    args: list[SType] = field(default_factory=list)
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        args = ", ".join(str(a) for a in self.args)
        return f"{self.name} {args}"

    def __hash__(self):
        return hash(self.name) + sum(hash(c) for c in self.args)


builtin_types = ["Top", "Bool", "Int", "Float", "String", "Unit"]


def get_type_vars(ty: SType) -> set[STypeVar]:
    match ty:
        case STypeVar(name):
            return {ty}
        case SAbstractionType(_, vtype, rtype):
            return get_type_vars(vtype).union(get_type_vars(rtype))
        case SRefinedType(_, rty, _):
            return get_type_vars(rty)
        case STypePolymorphism(name, _, body):
            return {t1 for t1 in get_type_vars(body) if t1.name != name}
        case SRefinementPolymorphism(name, _, body):
            return {t1 for t1 in get_type_vars(body) if t1.name != name}
        case STypeConstructor(name, args):
            return reduce(lambda acc, v: acc.union(get_type_vars(v)), args, set())
        case _:
            assert False, f"Unknown type ({ty}) ({type(ty)})"
