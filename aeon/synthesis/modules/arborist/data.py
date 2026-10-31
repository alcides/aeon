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
