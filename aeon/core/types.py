from __future__ import annotations

from abc import ABC
from dataclasses import dataclass, field
from enum import Enum

from aeon.core.liquid import LiquidLiteralFloat, LiquidLiteralInt, LiquidLiteralString, liquid_free_vars
from aeon.core.liquid import LiquidHole
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralUnit
from aeon.core.liquid import LiquidTerm
from aeon.core.multiplicity import Multiplicity, MOmega
from aeon.utils.location import Location, SynthesizedLocation
from aeon.utils.name import fresh_counter, Name


class Kind(Enum):
    BASE = "Β"
    STAR = "★"

    def __str__(self) -> str:
        return self.value

    def __repr__(self) -> str:
        return f"Kind.{self.name}"


class Type(ABC):
    loc: Location


@dataclass
class TypeVar(Type):
    name: Name
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __post_init__(self):
        if self.name.name in ["Int", "Bool"]:
            assert False

    def __repr__(self):
        return f"{self.name}"

    def __eq__(self, other):
        return type(other) is TypeVar and other.name == self.name

    def __hash__(self) -> int:
        return hash(self.name)


@dataclass
class Top(Type):
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __repr__(self):
        return "⊤"

    def __eq__(self, other):
        return type(other) is Top

    def __str__(self):
        return repr(self)

    def __hash__(self) -> int:
        return hash("Top")


@dataclass
class AbstractionType(Type):
    var_name: Name
    var_type: Type
    type: Type
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))
    multiplicity: Multiplicity = MOmega

    def __repr__(self):
        prefix = "" if self.multiplicity is MOmega else f"{self.multiplicity} "
        return f"({prefix}{self.var_name}:{self.var_type}) -> {self.type}"

    def __eq__(self, other):
        return (
            type(other) is AbstractionType
            and self.var_name == other.var_name
            and self.var_type == other.var_type
            and self.type == other.type
            and self.multiplicity is other.multiplicity
        )

    def __hash__(self) -> int:
        h = getattr(self, "_hash", None)
        if h is None:
            h = hash(self.var_name) + hash(self.var_type) + hash(self.type) + hash(self.multiplicity)
            object.__setattr__(self, "_hash", h)
        return h


@dataclass
class RefinedType(Type):
    name: Name
    type: TypeConstructor | TypeVar
    refinement: LiquidTerm
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __repr__(self):
        return f"{{ {self.name}:{self.type} | {self.refinement} }}"

    def __eq__(self, other):
        return (
            type(other) is RefinedType
            and self.name == other.name
            and self.type == other.type
            and self.refinement == other.refinement
        )

    def __hash__(self) -> int:
        h = getattr(self, "_hash", None)
        if h is None:
            h = hash(self.name) + hash(self.type) + hash(self.refinement)
            object.__setattr__(self, "_hash", h)
        return h


@dataclass
class TypePolymorphism(Type):
    name: Name  # alpha
    kind: Kind
    body: Type
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"forall {self.name}:{self.kind}, {self.body}"

    def __hash__(self) -> int:
        h = getattr(self, "_hash", None)
        if h is None:
            h = hash(self.name) + hash(self.kind) + hash(self.body)
            object.__setattr__(self, "_hash", h)
        return h


@dataclass
class RefinementPolymorphism(Type):
    name: Name
    sort: Type
    body: Type
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"forall <{self.name}:{self.sort}>, {self.body}"

    def __hash__(self) -> int:
        h = getattr(self, "_hash", None)
        if h is None:
            h = hash(self.name) + hash(self.sort) + hash(self.body)
            object.__setattr__(self, "_hash", h)
        return h


@dataclass
class TypeConstructor(Type):
    name: Name
    args: list[Type] = field(default_factory=list)
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        args = ", ".join(str(a) for a in self.args)
        return f"{self.name} {args}"

    def __eq__(self, other):
        return type(other) is TypeConstructor and other.name == self.name and self.args == other.args

    def __hash__(self) -> int:
        h = getattr(self, "_hash", None)
        if h is None:
            h = hash(self.name) + sum(hash(a) for a in self.args)
            object.__setattr__(self, "_hash", h)
        return h


@dataclass
class ExistentialType(Type):
    """Form B: a type wrapped with a list of existential binders.

    Each binder ``(name, ty)`` records that ``name`` is some witness of type
    ``ty`` (typically a ``RefinedType`` carrying everything we know about the
    value). The ``body`` is bare — a ``TypeConstructor``, ``TypeVar``, or
    ``AbstractionType`` — never another ``RefinedType`` and never another
    ``ExistentialType`` (binders are flat: nested existentials collapse).

    Lives at the top of a type only; transformations should peel and replace
    binders rather than nest them.
    """

    binders: tuple[tuple[Name, Type], ...]
    body: Type
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __post_init__(self):
        # Bodies must not themselves carry binders — flatten in constructors.
        assert not isinstance(self.body, ExistentialType), (
            "ExistentialType bodies must be flat; flatten via `with_binders`."
        )

    def __str__(self):
        bs = "; ".join(f"{n}:{t}" for (n, t) in self.binders)
        return f"[{bs}] {self.body}"

    def __eq__(self, other):
        return isinstance(other, ExistentialType) and self.binders == other.binders and self.body == other.body

    def __hash__(self) -> int:
        return hash(tuple(self.binders)) + hash(self.body)


def with_binders(extra: tuple[tuple[Name, Type], ...], ty: Type) -> Type:
    """Smart constructor: prepend ``extra`` binders, flattening any existing
    ``ExistentialType`` so the result is at most one wrapper deep."""
    if not extra:
        return ty
    if isinstance(ty, ExistentialType):
        return ExistentialType(tuple(extra) + tuple(ty.binders), ty.body, loc=ty.loc)
    return ExistentialType(tuple(extra), ty, loc=getattr(ty, "loc", SynthesizedLocation("default")))


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


# This class is here to prevent circular imports.


@dataclass
class LiquidHornApplication(LiquidTerm):
    name: Name
    argtypes: list[tuple[LiquidTerm, TypeConstructor | TypeVar]]
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __post_init__(self):
        assert isinstance(self.name, Name)
        for term, ty in self.argtypes:
            match term:
                case LiquidLiteralBool(_):
                    assert ty == TypeConstructor(Name("Bool", 0))
                case LiquidLiteralInt(_):
                    assert ty == TypeConstructor(Name("Int", 0))
                case LiquidLiteralFloat(_):
                    assert ty == TypeConstructor(Name("Float", 0))
                case LiquidLiteralString(_):
                    assert ty == TypeConstructor(Name("String", 0))
                case LiquidLiteralUnit():
                    assert ty == TypeConstructor(Name("Unit", 0))

    def __repr__(self):
        j = ", ".join([f"{n}:{t}" for (n, t) in self.argtypes])
        return f"?{self.name}({j})"

    def __eq__(self, other):
        return isinstance(other, LiquidHornApplication) and other.name == self.name

    def __hash__(self) -> int:
        return hash(self.name)


liq_true = LiquidLiteralBool(True)


def extract_parts(t: Type) -> tuple[Name, TypeConstructor | TypeVar, LiquidTerm]:
    assert (
        isinstance(t, TypeConstructor)
        or isinstance(t, RefinedType)
        or isinstance(
            t,
            TypeVar,
        )
        or isinstance(t, TypeConstructor)
    )
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
    """Returns the base type of a Refined Type"""
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
    elif isinstance(t, ExistentialType):
        binder_names = {bn for bn, _ in t.binders}
        bfv: list[Name] = []
        seen_so_far: set[Name] = set()
        for bn, bt in t.binders:
            for v in type_free_term_vars(bt):
                if v not in seen_so_far and v not in ALL_OPS:
                    bfv.append(v)
            seen_so_far.add(bn)
        body_fv = type_free_term_vars(t.body)
        return [x for x in bfv + body_fv if x not in binder_names and x not in ALL_OPS]
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
