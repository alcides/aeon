"""Lift a pure Aeon sketch over a packed language at its expression hole.

Every result carries the remaining language. In particular, applying a lambda
again (e.g. in a recursive fold) specializes the language retained by previous
calls, so all iterations and all examples must use one and the same body.
The combinator is interpreted from Aeon Core; there is no fold-name special case.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Iterator

from aeon.core.multiplicity import M0
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
from aeon.synthesis.api import SynthesisNotSuccessful, UnsupportedSynthesisGoal
from aeon.core.types import t_unit
from aeon.synthesis.modules.arborist.data import Algebraic, generated_inductives
from aeon.synthesis.modules.arborist.forest import Forest, OPERATORS, scalar_key
from aeon.utils.name import Name


@dataclass
class Closure:
    term: Abstraction
    environment: dict[Name, Any]


@dataclass(frozen=True)
class Primitive:
    name: str
    arguments: tuple[Any, ...] = ()


class LiftedInterpreter:
    def __init__(self, forest: Forest, definitions: dict[Name, Term], hole: Name, *, max_steps: int = 1_000_000):
        self.forest = forest
        self.definitions = definitions
        self.hole = hole
        self.max_steps = max_steps
        self.reachable: set[tuple] = set()
        self.inductives = generated_inductives(definitions)
        self.constructors = {p.name: p.arity for p in self.inductives.values() if not p.cases}

    def check_data(self, value: Any) -> None:
        """Bound constructor inputs and intermediate data before traversing them.

        Types of constructor literals are checked by the normal compiler. This
        additionally rejects opaque values, malformed tags/arities, unsupported
        leaves and oversized trees, including when called through the Python API.
        """
        remaining = 128

        def visit(current: Any, depth: int) -> None:
            nonlocal remaining
            self.forest.check_budget()
            remaining -= 1
            if remaining < 0 or depth > 32:
                raise SynthesisNotSuccessful("arborist data size limit exhausted")
            if type(current) is tuple:
                if not current or type(current[0]) is not str or self.constructors.get(current[0]) != len(current) - 1:
                    raise UnsupportedSynthesisGoal(
                        "arborist requires registered constructor values with matching arity"
                    )
                for field in current[1:]:
                    visit(field, depth + 1)
            else:
                scalar_key(current)

        visit(value, 0)

    def evaluate(self, term: Term, environment: dict[Name, Any], language: int) -> Iterator[tuple[Any, int]]:
        self.forest.check_budget()
        self.forest.stats.interpreter_steps += 1
        if self.forest.stats.interpreter_steps > self.max_steps:
            raise SynthesisNotSuccessful("arborist interpreter step limit exhausted")
        match term:
            case Literal(value, ty):
                if ty != t_unit or value is not None:
                    scalar_key(value)
                yield value, language
            case Var(name):
                if name in environment:
                    yield environment[name], language
                elif name in self.inductives:
                    primitive = self.inductives[name]
                    yield (primitive.name,) if primitive.arity == 0 else primitive, language
                elif name in self.definitions:
                    # Definitions are closed over their lexical top-level scope,
                    # not the caller's local bindings. Names already have IDs.
                    yield from self.evaluate(self.definitions[name], {}, language)
                elif name.id == 0 and name.name in OPERATORS:
                    yield Primitive(name.name), language
                elif name == Name("unit", 0):
                    yield None, language
                else:
                    raise UnsupportedSynthesisGoal(f"arborist cannot interpret component {name.pretty()}")
            case Abstraction():
                yield Closure(term, environment), language
            case Application(fun, arg):
                for function, first in self.evaluate(fun, environment, language):
                    for value, second in self.evaluate(arg, environment, first):
                        yield from self.apply(function, value, second)
            case Let(name, value, body) | Rec(name, _, value, body):
                if term.multiplicity is M0:
                    yield from self.evaluate(body, environment | {name: None}, language)
                else:
                    for result, narrowed in self.evaluate(value, environment, language):
                        if isinstance(term, Rec) and isinstance(result, Closure):
                            result = Closure(result.term, dict(result.environment))
                            result.environment[name] = result
                        yield from self.evaluate(body, environment | {name: result}, narrowed)
            case If(condition, yes, no):
                for value, narrowed in self.evaluate(condition, environment, language):
                    if type(value) is not bool:
                        raise UnsupportedSynthesisGoal("arborist requires a Bool conditional")
                    yield from self.evaluate(yes if value else no, environment, narrowed)
            case Annotation(expr, _) | TypeApplication(expr, _) | RefinementApplication(expr, _):
                yield from self.evaluate(expr, environment, language)
            case TypeAbstraction(_, _, body) | RefinementAbstraction(_, _, body):
                yield from self.evaluate(body, environment, language)
            case Hole(name):
                if name != self.hole:
                    raise UnsupportedSynthesisGoal("arborist supports one expression hole")
                try:
                    bindings = {name: environment[name] for name in self.forest.variables}
                except KeyError as exc:
                    raise UnsupportedSynthesisGoal("arborist grammar variable is outside the runtime scope") from exc
                self.reachable.add(tuple(scalar_key(bindings[name]) for name in self.forest.variables))
                yield from self.forest.specialize(language, bindings)
            case _:
                raise UnsupportedSynthesisGoal(f"arborist does not support {term.__class__.__name__}")

    def apply(self, function: Any, argument: Any, language: int) -> Iterator[tuple[Any, int]]:
        if isinstance(function, Closure):
            yield from self.evaluate(
                function.term.body, function.environment | {function.term.var_name: argument}, language
            )
        elif isinstance(function, Primitive):
            args = (*function.arguments, argument)
            if len(args) == (1 if function.name == "!" else 2):
                for value in args:
                    scalar_key(value)
                result = OPERATORS[function.name](*args)
                scalar_key(result)
                yield result, language
            else:
                yield Primitive(function.name, args), language
        elif isinstance(function, Algebraic):
            args = (*function.arguments, argument)
            if len(args) < function.arity:
                yield replace(function, arguments=args), language
            elif not function.cases:
                value = (function.name, *args)
                self.check_data(value)
                yield value, language
            else:
                value, *handlers = args
                self.check_data(value)
                if type(value) is not tuple or value[0] not in function.cases:
                    raise UnsupportedSynthesisGoal("arborist eliminator received a value of another datatype")
                handler = handlers[function.cases.index(value[0])]
                yield from self.apply_many(handler, value[1:], language)
        else:
            raise UnsupportedSynthesisGoal("arborist requires an interpreted pure function")

    def apply_many(self, function: Any, arguments: tuple[Any, ...], language: int) -> Iterator[tuple[Any, int]]:
        if not arguments:
            yield function, language
        else:
            for value, narrowed in self.apply(function, arguments[0], language):
                yield from self.apply_many(value, arguments[1:], narrowed)

    def run(self, target: Name, inputs: list[Any], language: int) -> Iterator[tuple[Any, int]]:
        for value in inputs:
            self.check_data(value)
        for function, narrowed in self.evaluate(Var(target), {}, language):
            yield from self.apply_many(function, tuple(inputs), narrowed)
