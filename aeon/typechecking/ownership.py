"""Ownership of values and their curried results, inferred on the linked core.

Argument multiplicities alone do not describe a closure's environment. These
facts complement QTT usage counts: a value retaining an owner must itself be
bound/passed linearly, including when obtained through an alias or factory.
Borrowed environments carry owner identities, substituted at curried calls and
checked against the lexical scope of each binding by the usage checker.
No source type is rewritten, and annotations cannot erase the inferred facts.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable

from aeon.core.instantiation import type_substitution
from aeon.core.multiplicity import M0, M1, MN, MOmega, MBorrow, Multiplicity
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    Hole,
    If,
    Let,
    Literal,
    Rec,
    RefinementAbstraction,
    RefinementApplication,
    Term,
    TypeAbstraction,
    TypeApplication,
    Var,
)
from aeon.core.types import (
    AbstractionType,
    ExistentialType,
    RefinedType,
    RefinementPolymorphism,
    Type,
    TypeConstructor,
    TypePolymorphism,
    t_bool,
    t_float,
    t_int,
    t_string,
    t_unit,
)
from aeon.utils.name import Name
from aeon.prelude.prelude import typing_vars


def unwrapped(ty: Type | None) -> Type | None:
    while isinstance(ty, (ExistentialType, TypePolymorphism, RefinementPolymorphism, RefinedType)):
        ty = ty.type if isinstance(ty, RefinedType) else ty.body
    return ty


def can_retain(ty: Type | None) -> bool:
    """Scalar results cannot retain an environment or a resource handle."""
    ty = unwrapped(ty)
    return not (isinstance(ty, TypeConstructor) and ty in (t_bool, t_float, t_int, t_string, t_unit))


@dataclass(frozen=True)
class Ownership:
    owned: bool = False
    result: Ownership | None = None
    borrows: frozenset[Name] = frozenset()
    parameter: Name | None = None

    def retaining(self) -> Ownership:
        return Ownership(True, self.result, self.borrows, self.parameter)

    def substitute(self, name: Name | None, roots: frozenset[Name]) -> Ownership:
        """Instantiate a returned closure's dependency on a formal parameter."""
        borrows = (self.borrows - {name}) | roots if name in self.borrows else self.borrows
        result = self.result.substitute(name, roots) if self.result is not None else None
        return Ownership(self.owned, result, borrows, self.parameter)

    def borrowing(self, roots: frozenset[Name]) -> Ownership:
        """A curried borrowed argument lives through the remaining prefixes."""
        result = self.result
        if result is not None and result.result is not None:
            result = result.borrowing(roots)
        return Ownership(self.owned, result, self.borrows | roots, self.parameter)


def merge(left: Ownership, right: Ownership) -> Ownership:
    if left.parameter is not None and right.parameter is not None and left.parameter != right.parameter:
        right = right.substitute(right.parameter, frozenset({left.parameter}))
    result = left.result or right.result
    if left.result is not None and right.result is not None:
        result = merge(left.result, right.result)
    return Ownership(left.owned or right.owned, result, left.borrows | right.borrows, left.parameter or right.parameter)


@dataclass(frozen=True)
class _Binding:
    ty: Type | None
    ownership: Ownership
    quantity: Multiplicity = MOmega


@dataclass
class OwnershipFacts:
    linear_types: frozenset[Name]
    is_native: Callable[[Term], bool]
    values: dict[int, Ownership] = field(default_factory=dict)
    types: dict[int, Type] = field(default_factory=dict)
    references: dict[int, frozenset[Name]] = field(default_factory=dict)
    bindings: dict[Name, _Binding] = field(default_factory=dict)
    origins: dict[Name, Name] = field(default_factory=dict)
    borrowed_functions: set[Name] = field(default_factory=set)
    read_captures: Callable[[Term], frozenset[Name]] | None = None
    recursive: dict[Name, Ownership] = field(default_factory=dict)
    changed: bool = False

    def origin(self, name: Name) -> Name:
        return self.origins.get(name, name)

    def value(self, term: Term) -> Ownership:
        if id(term) in self.values:
            return self.values[id(term)]
        if isinstance(term, Var) and term.name in self.bindings:
            return self.bindings[term.name].ownership
        return Ownership()

    def borrow_roots(self, term: Term) -> frozenset[Name]:
        while isinstance(term, Annotation):
            term = term.expr
        value = self.value(term)
        roots = value.borrows
        if isinstance(term, Var):
            binding = self.bindings.get(term.name)
            if value.owned or (binding is not None and binding.quantity is M1):
                roots |= {self.origin(term.name)}
        return roots

    def from_type(self, ty: Type | None, *, linear: bool = False) -> Ownership:
        plain = unwrapped(ty)
        owned = linear or (isinstance(plain, TypeConstructor) and plain.name in self.linear_types)
        if isinstance(plain, AbstractionType):
            # A linear callback may return ownership; its caller must preserve
            # that obligation. An unrestricted callback promises reusable
            # function results unless the result type explicitly says linear.
            result = self.from_type(
                plain.type,
                linear=can_retain(plain.type) and (linear or plain.multiplicity is M1),
            )
            return Ownership(owned, result, parameter=plain.var_name)
        return Ownership(owned)

    def infer(self, term: Term, initial: dict[Name, Type]) -> None:
        env = {
            name: _Binding(ty, self.from_type(ty) if name in typing_vars else self.external_type(ty))
            for name, ty in initial.items()
        }
        self.bindings.update(env)
        # A recursive result is not automatically owning: e.g. List.append
        # returns ordinary reusable data. Propagate discovered obligations to
        # recursive calls until stable, including across mutual companions.
        while True:
            self.changed = False
            self._infer(term, env)
            if not self.changed:
                break

    def external_type(self, ty: Type | None) -> Ownership:
        """An unavailable implementation may allocate in its result."""
        shape = self.from_type(ty)
        plain = unwrapped(ty)
        if isinstance(plain, AbstractionType):
            return Ownership(
                shape.owned, self.from_type(plain.type, linear=can_retain(plain.type)), parameter=plain.var_name
            )
        return shape

    def recursive_shape(self, value: Ownership, ty: Type | None) -> Ownership:
        """Keep the fixed-point lattice finite even for opaque recursive results.

        A function returning Top can return itself, adding another result arrow
        on each traversal. At opaque leaves, conservatively collapse nested
        obligations instead of growing an unbounded profile.
        """
        plain = unwrapped(ty)
        if isinstance(plain, AbstractionType):
            result = self.recursive_shape(value.result or self.from_type(plain.type), plain.type)
            return Ownership(value.owned, result, value.borrows, value.parameter or plain.var_name)
        borrows = value.borrows
        nested = value.result
        while nested is not None:
            borrows |= nested.borrows
            nested = nested.result
        return Ownership(self.has_ownership(value), borrows=borrows)

    def specialize(self, value: Ownership, ty: Type | None) -> Ownership:
        """Instantiation may reveal scalar results or additional arrows."""
        plain = unwrapped(ty)
        if isinstance(plain, AbstractionType):
            result = value.result or self.from_type(plain.type, linear=value.owned and can_retain(plain.type))
            result = self.specialize(result, plain.type) if can_retain(plain.type) else Ownership()
            return Ownership(value.owned, result, value.borrows, value.parameter or plain.var_name)
        return value

    def _infer(
        self,
        term: Term,
        env: dict[Name, _Binding],
        expected: Type | None = None,
    ) -> tuple[Ownership, Type | None, frozenset[Name]]:
        refs: frozenset[Name] = frozenset()
        ty = expected
        value = self.from_type(ty)
        match term:
            case Var(name):
                binding = env.get(name)
                if binding is not None:
                    value, ty = binding.ownership, binding.ty
                refs = frozenset({name})
            case Literal(_, literal_type):
                ty = literal_type
                value = self.from_type(ty)
            case Annotation(expr, annotation):
                value, _, refs = self._infer(expr, env, annotation)
                ty = annotation
            case Abstraction(name, body):
                arrow = unwrapped(expected)
                arg_ty = arrow.var_type if isinstance(arrow, AbstractionType) else None
                result_ty = arrow.type if isinstance(arrow, AbstractionType) else None
                quantity = arrow.multiplicity if isinstance(arrow, AbstractionType) else MOmega
                argument = self.from_type(arg_ty, linear=quantity is M1)
                if quantity is MBorrow:
                    argument = Ownership(False, argument.result, parameter=argument.parameter).borrowing(
                        frozenset({name})
                    )
                    if isinstance(unwrapped(arg_ty), AbstractionType):
                        self.borrowed_functions.add(name)
                binding = _Binding(arg_ty, argument, quantity)
                self.bindings[name] = binding
                result, _, body_refs = self._infer(body, {**env, name: binding}, result_ty)
                if not can_retain(result_ty):
                    result = Ownership()
                refs = body_refs - {name}
                captures_resource = any(
                    ref in env
                    and (env[ref].ownership.owned or env[ref].ownership.borrows or env[ref].quantity in (M1, MBorrow))
                    for ref in refs
                )
                reads = (
                    self.read_captures(body) - {name}
                    if captures_resource and self.read_captures is not None
                    else frozenset()
                )
                owned = any(
                    ref in env and ref not in reads and (env[ref].ownership.owned or env[ref].quantity is M1)
                    for ref in refs
                )
                loans = frozenset(
                    self.origin(ref)
                    for ref in reads
                    if ref in env and (env[ref].ownership.owned or env[ref].quantity in (M1, MBorrow))
                )
                for ref in refs:
                    if ref in env:
                        loans |= env[ref].ownership.borrows
                value = Ownership(owned, result, loans, name)
            case Application(fun, arg):
                fn, fun_ty, fn_refs = self._infer(fun, env)
                arrow = unwrapped(fun_ty)
                arg_ty = arrow.var_type if isinstance(arrow, AbstractionType) else None
                quantity = arrow.multiplicity if isinstance(arrow, AbstractionType) else M1
                actual, _, arg_refs = self._infer(arg, env, arg_ty)
                if isinstance(arrow, AbstractionType):
                    ty = arrow.type
                refs = fn_refs | (arg_refs if quantity is not M0 else frozenset())
                value = (fn.result or self.from_type(ty)).substitute(fn.parameter, self.borrow_roots(arg))
                if can_retain(ty):
                    if fn.owned or (self.has_ownership(actual) and quantity in (M1, MN)):
                        value = value.retaining()
                    # Instantiating a polymorphic result can reveal arrows
                    # which were absent from its original ownership shape.
                    value = merge(value, self.from_type(ty, linear=value.owned))
                    if quantity is MBorrow and isinstance(unwrapped(ty), AbstractionType):
                        value = value.borrowing(self.borrow_roots(arg))
                else:
                    value = Ownership()
            case Let(name, val, body, _, quantity) | Rec(name, _, val, body, multiplicity=quantity):
                declared = term.var_type if isinstance(term, Rec) else None
                local = dict(env)
                if isinstance(term, Rec):
                    local[name] = _Binding(declared, self.recursive.get(name, self.from_type(declared)), quantity)
                    for companion in term.companions:
                        local[companion.name] = _Binding(
                            companion.type, self.recursive.get(companion.name, self.from_type(companion.type))
                        )
                actual, val_ty, val_refs = self._infer(val, local, declared)
                if isinstance(term, Rec) and val_refs & ({name} | {c.name for c in term.companions}):
                    previous = self.recursive.get(name, self.from_type(declared))
                    inferred = merge(previous, self.recursive_shape(actual, declared))
                    if inferred != previous:
                        self.recursive[name] = inferred
                        self.changed = True
                local[name] = _Binding(val_ty, actual, quantity)
                self.bindings[name] = local[name]
                alias = val
                while isinstance(alias, Annotation):
                    alias = alias.expr
                if isinstance(alias, Var) and (actual.owned or not isinstance(unwrapped(val_ty), AbstractionType)):
                    self.origins[name] = self.origin(alias.name)
                value, ty, body_refs = self._infer(body, local, expected)
                refs = (body_refs - {name}) | (val_refs - {name} if quantity is not M0 else frozenset())
            case If(cond, then, otherwise):
                _, _, cond_refs = self._infer(cond, env)
                left, left_ty, left_refs = self._infer(then, env, expected)
                right, right_ty, right_refs = self._infer(otherwise, env, expected)
                value, ty = merge(left, right), left_ty or right_ty
                refs = cond_refs | left_refs | right_refs
            case TypeApplication(body, actual):
                value, ty, refs = self._infer(body, env)
                while isinstance(ty, ExistentialType):
                    ty = ty.body
                if isinstance(ty, TypePolymorphism):
                    poly = ty
                    try:
                        ty = type_substitution(poly.body, poly.name, actual)
                    except (AssertionError, ValueError):
                        ty = poly.body
                value = self.specialize(value, ty)
            case RefinementApplication(body, _):
                value, ty, refs = self._infer(body, env)
                while isinstance(ty, ExistentialType):
                    ty = ty.body
                if isinstance(ty, RefinementPolymorphism):
                    ty = ty.body
            case TypeAbstraction(_, _, body) | RefinementAbstraction(_, _, body):
                inner_ty = expected.body if isinstance(expected, (TypePolymorphism, RefinementPolymorphism)) else None
                value, _, refs = self._infer(body, env, inner_ty)
            case Hole():
                pass
        if self.is_native(term):
            # FFI implementations are trusted against their declared type.
            # Native constructors are curried Python values, not resource
            # captures from the surrounding Aeon scope.
            ty = expected or ty
            value, refs = self.from_type(ty), frozenset()
        self.values[id(term)] = value
        self.references[id(term)] = refs
        if ty is not None:
            self.types[id(term)] = ty
        return value, ty, refs

    def fits(self, value: Ownership, ty: Type | None, quantity: Multiplicity) -> bool:
        """Do not hide ownership behind a reusable higher-order parameter."""
        if quantity is M0:
            return True
        expected = self.from_type(ty, linear=quantity in (M1, MN))
        while True:
            if value.owned and not expected.owned:
                return False
            if value.result is None:
                return True
            if expected.result is None:
                # An unrestricted abstract type cannot conceal a function
                # whose returned closures have ownership obligations.
                return quantity in (M1, MN) or not self.has_ownership(value.result)
            value, expected = value.result, expected.result

    @staticmethod
    def has_ownership(value: Ownership) -> bool:
        return value.owned or (value.result is not None and OwnershipFacts.has_ownership(value.result))
