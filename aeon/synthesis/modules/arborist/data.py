"""Interpret compiler-generated inductives without executing native Python.

Only exact constructor/eliminator definitions emitted by the inductive
desugaring pass are recognized. Registry names alone are insufficient: a user
can shadow a constructor or recursor with an ordinary function.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    Literal,
    RefinementAbstraction,
    RefinementApplication,
    Term,
    TypeAbstraction,
    TypeApplication,
    Var,
)
from aeon.utils.name import Name
from aeon.core.types import AbstractionType, TypeConstructor, TypePolymorphism
from aeon.typechecking.context import TypingContext
from aeon.verification.constructor_registry import (
    get_constructor_fields,
    get_constructor_groups,
    get_constructor_order,
)


@dataclass(frozen=True)
class Algebraic:
    name: str
    arity: int
    # Empty for a constructor; declaration order for an eliminator.
    cases: tuple[str, ...] = ()
    arguments: tuple[Any, ...] = ()


@dataclass(frozen=True)
class DictionaryValue:
    tag: str
    fields: tuple[Any, ...]


@dataclass(frozen=True)
class DictionaryProjection:
    tag: str
    index: int
    arity: int
    arguments: tuple[Any, ...] = ()


def generated_dictionary_projections(
    definitions: dict[Name, Term], ctx: TypingContext
) -> tuple[set[str], dict[Name, DictionaryProjection]]:
    """Recognize exactly the compiler's field access, without evaluating Python."""
    classes = {e.name: (get_constructor_order(e.name.name) or []) for e in ctx._constructor_entries() if e.is_typeclass}
    tags = {tag for constructors in classes.values() for tag in constructors}
    projections = {}
    for name, ty in ctx.concrete_vars():
        while isinstance(ty, TypePolymorphism):
            ty = ty.body
        if not isinstance(ty, AbstractionType) or not isinstance(ty.var_type, TypeConstructor):
            continue
        constructors = classes.get(ty.var_type.name, [])
        if len(constructors) != 1 or name not in definitions:
            continue
        body = erase(definitions[name])
        params = []
        while isinstance(body, (Abstraction, TypeAbstraction, RefinementAbstraction)):
            if isinstance(body, Abstraction):
                params.append(body.var_name.name)
            body = erase(body.body)
        if not params or not isinstance(body, Application) or erase(body.fun) != Var(Name("native", 0)):
            continue
        if not isinstance(body.arg, Literal):
            continue
        tag = constructors[0]
        for index in range(len(get_constructor_fields(tag) or [])):
            expected = f"{params[0]}[{index + 1}]" + "".join(f"({p})" for p in params[1:])
            if body.arg.value == expected:
                projections[name] = DictionaryProjection(tag, index, len(params))
    return tags, projections


def erase(term: Term) -> Term:
    while isinstance(term, (Annotation, TypeApplication, RefinementApplication)):
        term = term.expr if isinstance(term, Annotation) else term.body
    return term


def generated_inductives(definitions: dict[Name, Term]) -> dict[Name, Algebraic]:
    """Recognize the registered, hygienic definitions in this program's scope."""
    signatures: dict[str, Algebraic] = {}
    for type_name in get_constructor_groups():
        cases = tuple(get_constructor_order(type_name) or ())
        for tag in cases:
            signatures[tag] = Algebraic(tag, len(get_constructor_fields(tag) or []))
        signatures[type_name + "_rec"] = Algebraic(type_name + "_rec", len(cases) + 1, cases)

    recognized = {}
    for name, definition in definitions.items():
        signature = signatures.get(name.name)
        if signature is None:
            continue
        parameters = []
        body = erase(definition)
        while isinstance(body, (Abstraction, TypeAbstraction, RefinementAbstraction)):
            if isinstance(body, Abstraction):
                parameters.append(body.var_name.name)
            body = erase(body.body)
        if len(parameters) != signature.arity:
            continue
        if not isinstance(body, Application) or erase(body.fun) != Var(Name("native", 0)):
            continue
        if not isinstance(body.arg, Literal):
            continue
        if not signature.cases:
            expected = f"('{name.name}', {', '.join(parameters)})"
        else:
            target, *handlers = parameters
            expected = "(_ for _ in ()).throw(Exception('Invalid constructor'))"
            for tag, handler in reversed(list(zip(signature.cases, handlers))):
                fields = len(get_constructor_fields(tag) or [])
                branch = handler + "".join(f"({target}[{i + 1}])" for i in range(fields))
                expected = f"({branch} if {target}[0] == '{tag}' else {expected})"
        if body.arg.value == expected:
            recognized[name] = signature
    return recognized
