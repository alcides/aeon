from __future__ import annotations

from abc import ABC
from dataclasses import dataclass, field
from typing import MutableSequence

from aeon.core.liquid import LiquidTerm
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    Top,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
    builtin_core_types,
)
from aeon.core.types import Kind
from aeon.core.types import Type
from aeon.utils.name import Name


class TypingContextEntry(ABC):
    pass


@dataclass(unsafe_hash=True)
class VariableBinder(TypingContextEntry):
    name: Name
    type: Type

    def __repr__(self):
        return f"{self.name} : {self.type}"


@dataclass(unsafe_hash=True)
class UninterpretedBinder(TypingContextEntry):
    name: Name
    # ``type`` is an ``AbstractionType`` for plain uninterpreted predicates
    # (``def feats : (ds:Dataset) -> Int = uninterpreted``) and a
    # ``TypePolymorphism`` / ``RefinementPolymorphism`` wrapping one for
    # polymorphic uninterpreted projections (``def Pair_mk_fst : forall
    # a, forall b, (this:Pair a b) -> a = uninterpreted``). The
    # polymorphic shape is preserved so the typechecker can instantiate
    # at call sites; the SMT layer strips foralls and specialises per
    # call via ``_specialize_liquid_term``.
    type: Type

    def __repr__(self):
        return f"uninterpreted {self.name} : {self.type}"


@dataclass(unsafe_hash=True)
class ReflectedBinder(TypingContextEntry):
    name: Name
    type: AbstractionType
    params: tuple[Name, ...]
    body: LiquidTerm

    def __repr__(self):
        params = ", ".join(str(p) for p in self.params)
        return f"reflected {self.name}({params}) : {self.type}"


@dataclass(unsafe_hash=True)
class TypeBinder(TypingContextEntry):
    type_name: Name
    type_kind: Kind = Kind.STAR

    def __repr__(self):
        return f"type {self.type_name} {self.type_kind}"


@dataclass
class TypeConstructorBinder(TypingContextEntry):
    name: Name
    args: list[Name]  # cant hash
    rforalls: list[tuple[Name, Type]] = field(default_factory=list)

    def __repr__(self):
        if self.args:
            argsf = "(" + ", ".join(map(str, self.args)) + ")"
        else:
            argsf = ""
        if self.rforalls:
            rfs = " " + " ".join(f"forall <{n}:{s} -> Bool>" for (n, s) in self.rforalls)
        else:
            rfs = ""
        return f"type {self.name}{argsf}{rfs}"

    def __hash__(self):
        return hash(self.name) + hash(tuple(self.args))


@dataclass
class TypingContext:
    entries: MutableSequence[TypingContextEntry] = field(default_factory=list)
    trusted_names: frozenset[Name] = field(default_factory=frozenset)

    def __post_init__(self):
        for bt in builtin_core_types[::-1]:
            temp = TypeConstructorBinder(bt.name, [])
            if temp not in self.entries:
                self.entries.insert(0, temp)

    def __repr__(self):
        fields = "; ".join(map(repr, self.entries))
        return f"[[{fields}]]"

    def with_var(self, name: Name, type: Type) -> TypingContext:
        nentries = [e for e in self.entries] + [VariableBinder(name, type)]
        return TypingContext(nentries, trusted_names=self.trusted_names)

    def with_typevar(self, name: Name, kind: Kind) -> TypingContext:
        nentries = [e for e in self.entries] + [TypeBinder(name, kind)]
        return TypingContext(nentries, trusted_names=self.trusted_names)

    def type_of(self, name: Name) -> Type | None:
        for e in self.entries:
            match e:
                case VariableBinder(iname, ty) | UninterpretedBinder(iname, ty):
                    if iname == name:
                        return ty
                case ReflectedBinder(iname, ty, _, _):
                    if iname == name:
                        return ty
        return None

    def kind_of(self, ty: Type) -> Kind:
        match ty:
            case Top() | RefinedType(_, TypeConstructor(_), _) | RefinedType(_, TypeConstructor(_, _), _):
                return Kind.BASE
            case TypeVar(name):
                # Look up the kind the variable was bound with rather than
                # assuming ``BASE``. Polytypes introduce type variables of
                # higher kind (e.g. ``* -> *``), so the binder is the source
                # of truth here.
                for tv_name, tv_kind in self.typevars():
                    if tv_name == name:
                        return tv_kind
                assert False, f"TypeVar {name} not found in context type variables {self.typevars()}"
            case RefinedType(_, TypeVar(name), _):
                assert (name, Kind.BASE) in self.typevars(), f"{name} not in {self.typevars()}"
                return Kind.BASE
            case AbstractionType(_, _, _):
                return Kind.STAR
            case TypePolymorphism(_, _, _):
                return Kind.STAR
            case TypeConstructor(_, _):
                return Kind.BASE
            case _:
                assert False, f"Unknown type in context: {ty}"

    def typevars(self) -> list[tuple[Name, Kind]]:
        return [(e.type_name, e.type_kind) for e in self.entries if isinstance(e, TypeBinder)]

    def vars(self) -> list[tuple[Name, Type]]:
        return [
            (e.name, e.type)
            for e in self.entries
            if isinstance(e, VariableBinder) or isinstance(e, UninterpretedBinder) or isinstance(e, ReflectedBinder)
        ]

    def concrete_vars(self) -> list[tuple[Name, Type]]:
        """Concrete term variables in scope, honoring lexical shadowing.

        ``with_var`` appends, so entries run outermost→innermost. When a surface
        name is bound more than once (an inner ``let`` shadowing an outer
        binding), only the innermost binding is referenceable by that name, so
        we keep the last occurrence per name string. This is what every
        synthesis consumer wants — the set of variables actually reachable at a
        program point — and it is what lets a shadowing ``let`` hide an outer
        binding from the synthesizer's grammar.
        """
        latest: dict[str, tuple[Name, Type]] = {}
        for e in self.entries:
            if isinstance(e, VariableBinder):
                latest[e.name.name] = (e.name, e.type)
        return list(latest.values())

    def has_uninterpreted_fun(self, name) -> bool:
        return name in [e.name for e in self.entries if isinstance(e, UninterpretedBinder)]

    def get_type_constructor(self, name: Name) -> list[Name] | None:
        # Built-in type constructors (``Unit``, ``Int``, ``Bool``, ``Float``,
        # ``String``, ``Set``, ...) are entered as ``TypeConstructorBinder``
        # entries in ``__post_init__``, so there is no need for a hardcoded
        # escape hatch here — the context is the single source of truth.
        for entry in self.entries[::-1]:
            match entry:
                case TypeConstructorBinder(ename, eargs):
                    if ename == name:
                        return eargs
        return None

    def __hash__(self):
        return sum(hash(e) for e in self.entries)
