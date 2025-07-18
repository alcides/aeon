from abc import ABC
from dataclasses import dataclass, field
from functools import reduce

from aeon.core.types import Kind

from typing import TYPE_CHECKING


from aeon.utils.location import Location, SynthesizedLocation
from aeon.utils.name import Name


if TYPE_CHECKING:
    from aeon.sugar.program import STerm, sterm_pretty


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
        case STypeConstructor(name, args):
            return reduce(lambda acc, v: acc.union(get_type_vars(v)), args, set())
        case _:
            assert False, f"Unknown type ({ty}) ({type(ty)})"


def stype_pretty(stype: SType) -> str:
    match stype:
        case STypeVar(name=name):
            return f"'{name.pretty()}"
        case SRefinedType(name=name, type=type, refinement=ref):
            inner_pretty = stype_pretty(type)
            ref_pretty = sterm_pretty(ref)
            return f"{{{name.pretty()} : {inner_pretty} | {ref_pretty} }}"
        case SAbstractionType(var_name=vn, var_type=vt, type=rt):
            vt_pretty = stype_pretty(vt)
            rt_pretty = stype_pretty(rt)
            return f"({vn.pretty()} : {vt_pretty}) -> {rt_pretty}"
        case STypePolymorphism(name=name, kind=kind, body=body):
            body_pretty = stype_pretty(body)
            return f"∀{name.pretty()}:{kind}. {body_pretty}"
        case STypeConstructor(name=name, args=args):
            if not args:
                return name.pretty()
            args_str = " ".join(stype_pretty(arg) for arg in args)
            return f"{name.pretty()} {args_str}"
        case _:
            return str(stype)
