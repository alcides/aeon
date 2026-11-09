"""Backend-independent specialization of dictionary-passing components.

Search sees ordinary monomorphic bindings. Before validation, evaluation or
returning a solution, those bindings expand to checked Core type/dictionary
applications. Class identity comes from compiler declarations, not name guesses.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from time import monotonic
from typing import Iterator

from aeon.core.equality import core_type_equality
from aeon.core.instantiation import type_substitution
from aeon.core.substitutions import substitution, substitution_in_type
from aeon.core.terms import Application, Term, TypeApplication, Var
from aeon.core.types import (
    AbstractionType,
    ArrowKind,
    Kinding,
    RefinedType,
    RefinementPolymorphism,
    Type,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
    kind_compatible,
    t_bool,
    t_float,
    t_int,
    t_string,
)
from aeon.typechecking.context import TypingContext, VariableBinder
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name, fresh_counter
from aeon.verification.constructor_registry import get_constructor_order


def _shape(ty: Type) -> Type:
    if isinstance(ty, RefinedType):
        return _shape(ty.type)
    if isinstance(ty, TypeConstructor):
        return TypeConstructor(ty.name, [_shape(a) for a in ty.args])
    if isinstance(ty, AbstractionType):
        return replace(ty, var_type=_shape(ty.var_type), type=_shape(ty.type))
    return ty


def _kind(ctx: TypingContext, ty: Type) -> Kinding | None:
    """Reject out-of-scope variables even inside a function-type argument."""
    if isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
        return None
    if isinstance(ty, AbstractionType):
        domain, codomain = _kind(ctx, ty.var_type), _kind(ctx, ty.type)
        if domain is None or codomain is None or isinstance(domain, ArrowKind) or isinstance(codomain, ArrowKind):
            return None
    try:
        return ctx.kind_of(ty)
    except (ValueError, AssertionError):
        return None


def type_universe(ctx: TypingContext, goal: Type) -> tuple[Type, ...]:
    """In-scope types and constructors, including partial applications.

    No constructed tower of types is enumerated. Scoped abstract variables and
    each prefix of types already mentioned by the program supply higher kinds.
    """
    result: dict[str, Type] = {}

    def add(ty: Type) -> None:
        ty = _shape(ty)
        if _kind(ctx, ty) is not None:
            result.setdefault(repr(ty), ty)

    def visit(ty: Type) -> None:
        if isinstance(ty, RefinedType):
            visit(ty.type)
        elif isinstance(ty, TypeConstructor):
            for i in range(len(ty.args) + 1):
                add(TypeConstructor(ty.name, ty.args[:i]))
            for arg in ty.args:
                visit(arg)
        elif isinstance(ty, AbstractionType):
            add(ty)
            visit(ty.var_type)
            visit(ty.type)
        elif isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
            visit(ty.body)
        elif isinstance(ty, TypeVar):
            add(ty)

    # Put hole-local types first; limits imposed by a backend must not hide them
    # behind the prelude's concrete instantiations.
    for name, _ in ctx.typevars():
        add(TypeVar(name))
    visit(goal)
    for _, ty in reversed(ctx.concrete_vars()):
        visit(ty)
    for ty in (t_int, t_bool, t_float, t_string):
        add(ty)
    for declaration in ctx._constructor_entries():
        add(TypeConstructor(declaration.name))
    return tuple(result.values())


def match_types(
    ctx: TypingContext,
    pattern: Type,
    actual: Type,
    parameters: dict[Name, Kinding],
    substitutions: dict[Name, Type],
) -> bool:
    """Match all head arguments, respecting repeated variables and their kinds.

    Matching ``f a`` against ``Pair Int Bool`` binds ``f`` to ``Pair Int`` and
    ``a`` to ``Bool``. The surrounding context's variables remain rigid.
    """
    pattern, actual = _shape(pattern), _shape(actual)

    def bind(name: Name, value: Type) -> bool:
        kind = _kind(ctx, value)
        if kind is None or not kind_compatible(kind, parameters[name]):
            return False
        if name in substitutions:
            return core_type_equality(substitutions[name], value)
        substitutions[name] = value
        return True

    if isinstance(pattern, TypeVar) and pattern.name in parameters:
        return bind(pattern.name, actual)
    if isinstance(pattern, TypeConstructor) and pattern.name in parameters:
        if not pattern.args:
            return bind(pattern.name, actual)
        if not isinstance(actual, TypeConstructor) or len(actual.args) < len(pattern.args):
            return False
        boundary = len(actual.args) - len(pattern.args)
        if not bind(pattern.name, TypeConstructor(actual.name, actual.args[:boundary])):
            return False
        return all(
            match_types(ctx, p, a, parameters, substitutions) for p, a in zip(pattern.args, actual.args[boundary:])
        )
    if isinstance(pattern, TypeConstructor) and isinstance(actual, TypeConstructor):
        return (
            pattern.name == actual.name
            and len(pattern.args) == len(actual.args)
            and all(match_types(ctx, p, a, parameters, substitutions) for p, a in zip(pattern.args, actual.args))
        )
    if isinstance(pattern, AbstractionType) and isinstance(actual, AbstractionType):
        return match_types(ctx, pattern.var_type, actual.var_type, parameters, substitutions) and match_types(
            ctx, pattern.type, actual.type, parameters, substitutions
        )
    return core_type_equality(pattern, actual)


def _schema(ty: Type) -> tuple[dict[Name, Kinding], Type]:
    parameters = {}
    while isinstance(ty, TypePolymorphism):
        parameters[ty.name] = ty.kind
        ty = ty.body
    return parameters, ty


def _type_size(ty: Type) -> int:
    if isinstance(ty, RefinedType):
        return _type_size(ty.type)
    if isinstance(ty, TypeConstructor):
        return 1 + sum(_type_size(arg) for arg in ty.args)
    if isinstance(ty, AbstractionType):
        return 1 + _type_size(ty.var_type) + _type_size(ty.type)
    return 1


def _apply_types(term: Term, ty: Type, arguments: dict[Name, Type]) -> tuple[Term, Type]:
    while isinstance(ty, TypePolymorphism) and ty.name in arguments:
        argument = arguments[ty.name]
        term = TypeApplication(term, argument)
        ty = type_substitution(ty.body, ty.name, argument)
    return term, ty


class DictionaryResolver:
    """Resolve scoped dictionaries, superclass projections and prerequisites.

    Only already checked dictionary values and functions whose inputs are all
    dictionaries count as evidence. Dictionary constructors are excluded: search
    must not fabricate a new instance while selecting a method implementation.
    """

    def __init__(
        self,
        ctx: TypingContext,
        universe: tuple[Type, ...],
        deadline: float = float("inf"),
        *,
        given: frozenset[Name] = frozenset(),
        exclude: frozenset[Name] = frozenset(),
    ):
        self.ctx, self.universe, self.deadline = ctx, universe, deadline
        self.given = given
        self.classes = {e.name for e in ctx._constructor_entries() if e.is_typeclass}
        constructors = {n for c in self.classes for n in (get_constructor_order(c.name) or [])}
        self.values: list[tuple[Term, Type]] = []
        self.providers: list[tuple[Name, Type]] = []
        self.cache: dict[tuple[str, bool], Term] = {}
        for name, ty in ctx.concrete_vars():
            if name.name in constructors or name in exclude:
                continue
            if self.is_dictionary(ty):
                self.values.append((Var(name), ty))
                continue
            _, body = _schema(ty)
            while isinstance(body, AbstractionType) and self.is_dictionary(body.var_type):
                body = body.type
            if self.is_dictionary(body):
                self.providers.append((name, ty))

    def is_dictionary(self, ty: Type) -> bool:
        base = ty.type if isinstance(ty, RefinedType) else ty
        return isinstance(base, TypeConstructor) and base.name in self.classes

    def _checked(self, term: Term, goal: Type) -> bool:
        try:
            return check_type(self.ctx, term, goal)
        except (AssertionError, ValueError, NotImplementedError):
            return False

    def resolve(self, goal: Type) -> Term | None:
        # Projecting a given superclass must beat selecting a global instance.
        if self.given:
            local = self._resolve(goal, only_given=True)
            if local is not None:
                return local
        return self._resolve(goal)

    def _resolve(
        self,
        goal: Type,
        trail: tuple[str, ...] = (),
        providers: tuple[tuple[Name, int], ...] = (),
        *,
        only_given: bool = False,
    ) -> Term | None:
        if monotonic() >= self.deadline:
            return None
        key = repr(goal)
        if (key, only_given) in self.cache:
            return self.cache[key, only_given]
        if key in trail or not self.is_dictionary(goal):
            return None
        # A lexical parameter takes precedence over a top-level instance.
        for term, ty in reversed(self.values):
            if only_given and isinstance(term, Var) and term.name not in self.given:
                continue
            if core_type_equality(_shape(ty), _shape(goal)) and self._checked(term, goal):
                self.cache[key, only_given] = term
                return term
        for name, ty in self.providers:
            size = _type_size(goal)
            if any(previous == name and size >= old_size for previous, old_size in providers):
                continue
            parameters, result = _schema(ty)
            if only_given and not isinstance(result, AbstractionType) and name not in self.given:
                continue
            while isinstance(result, AbstractionType):
                result = result.type
            bindings: dict[Name, Type] = {}
            if not match_types(self.ctx, result, goal, parameters, bindings):
                continue
            for args in self._arguments(parameters, bindings):
                term, current = _apply_types(Var(name), ty, args)
                while isinstance(current, AbstractionType):
                    evidence = self._resolve(
                        current.var_type, (*trail, key), (*providers, (name, size)), only_given=only_given
                    )
                    if evidence is None:
                        break
                    term = Application(term, evidence)
                    current = substitution_in_type(current.type, evidence, current.var_name)
                else:
                    if self._checked(term, goal):
                        self.cache[key, only_given] = term
                        return term
        return None

    def _arguments(self, parameters: dict[Name, Kinding], initial: dict[Name, Type]) -> Iterator[dict[Name, Type]]:
        remaining = [(n, k) for n, k in parameters.items() if n not in initial]

        def visit(index: int, chosen: dict[Name, Type]) -> Iterator[dict[Name, Type]]:
            if monotonic() >= self.deadline:
                return
            if index == len(remaining):
                yield chosen
                return
            name, expected = remaining[index]
            for ty in self.universe:
                kind = _kind(self.ctx, ty)
                if kind is not None and kind_compatible(kind, expected):
                    yield from visit(index + 1, chosen | {name: ty})

        yield from visit(0, initial)


@dataclass
class TypeclassComponents:
    context: TypingContext
    definitions: dict[Name, Term] = field(default_factory=dict)

    def expand(self, candidate: Term) -> Term:
        for name, definition in self.definitions.items():
            candidate = substitution(candidate, definition, name)
        return candidate


def prepare_typeclass_components(
    ctx: TypingContext,
    goal: Type,
    *,
    exclude: frozenset[Name] = frozenset(),
    owner: Name | None = None,
    deadline: float = float("inf"),
) -> TypeclassComponents:
    """Expose instantiated methods with their dictionary arguments discharged."""
    prepared = TypeclassComponents(ctx)
    if monotonic() >= deadline or not any(e.is_typeclass for e in ctx._constructor_entries()):
        return prepared
    universe = type_universe(ctx, goal)
    owner = owner if owner is not None else next(iter(exclude)) if len(exclude) == 1 else None
    local: set[Name] = set()
    in_body = False
    for name, _ in ctx.vars():
        if name == owner:
            in_body = True
        elif in_body:
            local.add(name)
    resolver = DictionaryResolver(ctx, universe, deadline, given=frozenset(local), exclude=exclude)
    entries = list(ctx.entries)
    values = [(Var(n), t) for n, t in ctx.concrete_vars() if n not in exclude]

    def publish(term: Term, ty: Type, method: Name) -> None:
        identifier = fresh_counter.fresh()
        alias = Name(f"_method_{method.name}_{identifier}", identifier)
        prepared.definitions[alias] = term
        entries.append(VariableBinder(alias, ty))

    def available_calls(term: Term, ty: Type) -> Iterator[tuple[Term, Type]]:
        """Scalar-only grammars can also select calls on existing inputs.

        This supplies leaves, not a second recursive search: arguments come
        only from the original context, never from other generated calls.
        """
        if monotonic() >= deadline:
            return
        if not isinstance(ty, AbstractionType):
            if core_type_equality(_shape(ty), _shape(goal)):
                yield term, ty
            return
        for value, value_type in values:
            if core_type_equality(_shape(value_type), _shape(ty.var_type)) and resolver._checked(value, ty.var_type):
                yield from available_calls(Application(term, value), substitution_in_type(ty.type, value, ty.var_name))

    for name, ty in ctx.concrete_vars():
        if name in exclude:
            continue
        parameters, body = _schema(ty)
        if not isinstance(body, AbstractionType) or not resolver.is_dictionary(body.var_type):
            continue

        # Resolve as soon as all variables in a constraint are instantiated,
        # before enumerating a method's unrelated polymorphic arguments.
        def instantiate(term: Term, current: Type) -> Iterator[tuple[Term, Type]]:
            if monotonic() >= deadline:
                return
            _, tail = _schema(current)
            if isinstance(tail, AbstractionType) and resolver.is_dictionary(tail.var_type):
                if _kind(ctx, tail.var_type) is not None and resolver.resolve(tail.var_type) is None:
                    return
            if isinstance(current, TypePolymorphism):
                for argument in universe:
                    kind = _kind(ctx, argument)
                    if kind is not None and kind_compatible(kind, current.kind):
                        yield from instantiate(
                            TypeApplication(term, argument), type_substitution(current.body, current.name, argument)
                        )
            else:
                while isinstance(current, AbstractionType) and resolver.is_dictionary(current.var_type):
                    evidence = resolver.resolve(current.var_type)
                    if evidence is None:
                        return
                    term = Application(term, evidence)
                    current = substitution_in_type(current.type, evidence, current.var_name)
                if not isinstance(current, (TypePolymorphism, RefinementPolymorphism)):
                    yield term, current

        for term, specialized_type in instantiate(Var(name), ty):
            publish(term, specialized_type, name)
            if isinstance(specialized_type, AbstractionType):
                result: Type = specialized_type
                while isinstance(result, AbstractionType):
                    result = result.type
                if core_type_equality(_shape(result), _shape(goal)):
                    for call, result_type in available_calls(term, specialized_type):
                        publish(call, result_type, name)
    if prepared.definitions:
        prepared.context = replace(ctx, entries=entries)
    return prepared
