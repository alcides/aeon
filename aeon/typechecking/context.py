from __future__ import annotations

from abc import ABC
from dataclasses import dataclass, field
from itertools import chain
from operator import index as integer_index
from typing import Iterable, MutableSequence, SupportsIndex

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
    linear: bool = False
    """Declared as ``linear type``: binders of this type must be at multiplicity 1."""

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


class _ContextEntries(list[TypingContextEntry]):
    """Owned derived entries with a mutation-aware constructor-only view.

    Variable/type-variable extensions share the view, not a global cache. Keep
    actual binder objects so updates to a declaration's name or args stay live.
    """

    def __init__(self, values: Iterable[TypingContextEntry], constructors: tuple[TypeConstructorBinder, ...] | None):
        super().__init__(values)
        self._constructors = constructors

    def constructors(self) -> tuple[TypeConstructorBinder, ...]:
        if self._constructors is None:
            self._constructors = tuple(e for e in self if isinstance(e, TypeConstructorBinder))
        return self._constructors

    def append(self, value):
        self._constructors = None
        return super().append(value)

    def extend(self, values):
        self._constructors = None
        return super().extend(values)

    def insert(self, index, value):
        self._constructors = None
        return super().insert(index, value)

    def __setitem__(self, index, value):
        self._constructors = None
        return super().__setitem__(index, value)

    def __delitem__(self, index):
        self._constructors = None
        return super().__delitem__(index)

    def clear(self):
        self._constructors = None
        return super().clear()

    def pop(self, index=-1):
        self._constructors = None
        return super().pop(index)

    def remove(self, value):
        self._constructors = None
        return super().remove(value)

    def reverse(self):
        self._constructors = None
        return super().reverse()

    def sort(self, *args, **kwargs):
        self._constructors = None
        return super().sort(*args, **kwargs)

    # list's + overload widens element types; += preserves the list's type.
    def __iadd__(self, values: Iterable[TypingContextEntry]) -> _ContextEntries:  # type: ignore[override, misc]
        self._constructors = None
        super().__iadd__(values)
        return self

    def __imul__(self, count: SupportsIndex) -> _ContextEntries:
        self._constructors = None
        super().__imul__(count)
        return self


class _ContextSnapshot(MutableSequence[TypingContextEntry]):
    """Chunked, copy-on-write entries for cheap lexical scope extension.

    Chunks contain the original binder objects, just as copying a list does.
    Structural mutations materialize a private list; already derived contexts
    keep their snapshots. No context or mutable declaration is globally cached.
    """

    _CHUNK_SIZE = 32

    def __init__(
        self,
        blocks: tuple[tuple[TypingContextEntry, ...], ...],
        tail: tuple[TypingContextEntry, ...],
        constructors: tuple[TypeConstructorBinder, ...],
    ) -> None:
        self._blocks: tuple[tuple[TypingContextEntry, ...], ...] = blocks
        self._tail: tuple[TypingContextEntry, ...] = tail
        self._constructors: tuple[TypeConstructorBinder, ...] = constructors
        self._mutable: _ContextEntries | None = None

    @classmethod
    def extend_scope(
        cls,
        entries: MutableSequence[TypingContextEntry],
        binder: TypingContextEntry,
        constructors: tuple[TypeConstructorBinder, ...],
    ) -> _ContextSnapshot:
        if isinstance(entries, cls):
            entries._freeze()
            blocks, tail = entries._blocks, entries._tail
        else:
            values = tuple(entries)
            boundary = len(values) // cls._CHUNK_SIZE * cls._CHUNK_SIZE
            blocks = tuple(values[i : i + cls._CHUNK_SIZE] for i in range(0, boundary, cls._CHUNK_SIZE))
            tail = values[boundary:]
        tail = (*tail, binder)
        if len(tail) == cls._CHUNK_SIZE:
            blocks, tail = (*blocks, tail), ()
        return cls(blocks, tail, constructors)

    def _freeze(self) -> None:
        if self._mutable is not None:
            values = tuple(self._mutable)
            boundary = len(values) // self._CHUNK_SIZE * self._CHUNK_SIZE
            self._blocks = tuple(values[i : i + self._CHUNK_SIZE] for i in range(0, boundary, self._CHUNK_SIZE))
            self._tail = values[boundary:]
            self._constructors = self._mutable.constructors()
            self._mutable = None

    def _writable(self) -> _ContextEntries:
        if self._mutable is None:
            self._mutable = _ContextEntries(self, self._constructors)
        return self._mutable

    def constructors(self) -> tuple[TypeConstructorBinder, ...]:
        return self._mutable.constructors() if self._mutable is not None else self._constructors

    def __len__(self):
        if self._mutable is not None:
            return len(self._mutable)
        return len(self._blocks) * self._CHUNK_SIZE + len(self._tail)

    def __iter__(self):
        if self._mutable is not None:
            return iter(self._mutable)
        return chain(chain.from_iterable(self._blocks), self._tail)

    def __getitem__(self, index):
        if self._mutable is not None:
            return self._mutable[index]
        if isinstance(index, slice):
            return list(self)[index]
        index = integer_index(index)
        if index < 0:
            index += len(self)
        if not 0 <= index < len(self):
            raise IndexError("context entry index out of range")
        block, offset = divmod(index, self._CHUNK_SIZE)
        return self._tail[offset] if block == len(self._blocks) else self._blocks[block][offset]

    def __setitem__(self, index, value):
        self._writable()[index] = value

    def __delitem__(self, index):
        del self._writable()[index]

    def insert(self, index, value):
        self._writable().insert(index, value)

    def reverse(self):
        self._writable().reverse()

    def sort(self, *args, **kwargs):
        self._writable().sort(*args, **kwargs)

    def __imul__(self, count: SupportsIndex):
        self._writable().__imul__(count)
        return self

    def __eq__(self, other):
        if not isinstance(other, (list, _ContextSnapshot)):
            return NotImplemented
        return list(self) == list(other)


@dataclass
class TypingContext:
    entries: MutableSequence[TypingContextEntry] = field(default_factory=list)
    trusted_names: frozenset[Name] = field(default_factory=frozenset)
    # When False, skip re-injecting builtins (used by with_var / with_typevar so
    # synthesis-time extensions do not re-scan ``entries`` for each binder).
    _ensure_builtins: bool = field(default=True, repr=False, compare=False)

    def __post_init__(self):
        if not self._ensure_builtins:
            return
        for bt in builtin_core_types[::-1]:
            temp = TypeConstructorBinder(bt.name, [])
            if temp not in self.entries:
                self.entries.insert(0, temp)

    def __repr__(self):
        fields = "; ".join(map(repr, self.entries))
        return f"[[{fields}]]"

    def with_var(self, name: Name, type: Type) -> TypingContext:
        """Extend with a variable binder; shares trust set and skips builtin re-scan."""
        return TypingContext(
            _ContextSnapshot.extend_scope(self.entries, VariableBinder(name, type), self._constructor_entries()),
            trusted_names=self.trusted_names,
            _ensure_builtins=False,
        )

    def with_typevar(self, name: Name, kind: Kind) -> TypingContext:
        """Extend with a type variable; shares trust set and skips builtin re-scan."""
        return TypingContext(
            _ContextSnapshot.extend_scope(self.entries, TypeBinder(name, kind), self._constructor_entries()),
            trusted_names=self.trusted_names,
            _ensure_builtins=False,
        )

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

    def _constructor_entries(self) -> tuple[TypeConstructorBinder, ...]:
        if isinstance(self.entries, (_ContextEntries, _ContextSnapshot)):
            return self.entries.constructors()
        return tuple(e for e in self.entries if isinstance(e, TypeConstructorBinder))

    def get_type_constructor(self, name: Name) -> list[Name] | None:
        # Built-in type constructors (``Unit``, ``Int``, ``Bool``, ``Float``,
        # ``String``, ``Set``, ...) are entered as ``TypeConstructorBinder``
        # entries in ``__post_init__``, so there is no need for a hardcoded
        # escape hatch here — the context is the single source of truth.
        for entry in reversed(self._constructor_entries()):
            if entry.name == name:
                return entry.args
        return None

    def __hash__(self):
        return sum(hash(e) for e in self.entries)
