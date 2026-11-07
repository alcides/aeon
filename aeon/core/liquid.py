from __future__ import annotations

from abc import ABC
from collections.abc import Sequence
from dataclasses import dataclass, field
from aeon.utils.location import Location, SynthesizedLocation
from aeon.utils.name import Name


class LiquidTerm(ABC):
    loc: Location


@dataclass(frozen=True)
class LiquidPredicate:
    """A datatype predicate argument: a curried lambda or a predicate name.

    Parameter sorts come from the datatype declaration, just as for a term
    lambda checked against a function type. These arguments are erased at runtime.
    """

    parameters: tuple[Name, ...]
    body: LiquidTerm
    implicit: bool = False

    def __str__(self):
        return "".join(f"fun {p} => " for p in self.parameters) + str(self.body)

    def apply(self, arguments: Sequence[LiquidTerm]) -> LiquidTerm:
        from aeon.core.substitutions import substitution_in_liquid
        from aeon.utils.name import fresh_counter

        if not self.parameters and isinstance(self.body, LiquidVar):
            return LiquidApp(self.body.name, list(arguments))
        if len(arguments) != len(self.parameters):
            raise ValueError("Datatype predicate argument has the wrong arity")
        # Simultaneous substitution: actual arguments may use a formal's name.
        fresh = [Name("predicate_arg", fresh_counter.fresh()) for _ in arguments]
        body = self.body
        for parameter, witness in zip(self.parameters, fresh):
            body = substitution_in_liquid(body, LiquidVar(witness), parameter)
        for witness, argument in zip(fresh, arguments):
            body = substitution_in_liquid(body, argument, witness)
        return body

    def substitute(self, replacement: LiquidTerm, name: Name) -> LiquidPredicate:
        from aeon.core.substitutions import substitution_in_liquid
        from aeon.utils.name import fresh_counter

        if name in self.parameters:
            return self
        body = self.body
        parameters = list(self.parameters)
        free = liquid_free_vars(replacement)
        for index, parameter in enumerate(parameters):
            if parameter in free:
                fresh = Name(parameter.name, fresh_counter.fresh())
                body = substitution_in_liquid(body, LiquidVar(fresh), parameter)
                parameters[index] = fresh
        return LiquidPredicate(tuple(parameters), substitution_in_liquid(body, replacement, name), self.implicit)


def ensure_liqterm(a: LiquidTerm | Name) -> LiquidTerm:
    if isinstance(a, Name):
        return LiquidVar(a)
    return a


class LiquidHole(LiquidTerm):
    def __eq__(self, other):
        return isinstance(other, self.__class__)


def is_safe_for_application(x: LiquidTerm):
    return (
        isinstance(x, LiquidVar)
        or isinstance(x, LiquidLiteralBool)
        or isinstance(x, LiquidLiteralFloat)
        or isinstance(x, LiquidLiteralInt)
        or isinstance(x, LiquidLiteralString)
        or isinstance(x, LiquidLiteralUnit)
    )


@dataclass
class LiquidLiteralUnit(LiquidTerm):
    """The single inhabitant of the Unit type.

    Distinct from LiquidLiteralBool(True): Unit has its own SMT sort with
    exactly one element, so ``unit == True`` is ill-typed and rejected at
    the liquid layer rather than silently true at the SMT layer.
    """

    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __repr__(self):
        return "()"

    def __eq__(self, other):
        return isinstance(other, LiquidLiteralUnit)

    def __hash__(self) -> int:
        return hash("()")


@dataclass
class LiquidLiteralBool(LiquidTerm):
    value: bool
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __repr__(self):
        return f"{self.value}".lower()

    def __eq__(self, other):
        return isinstance(other, LiquidLiteralBool) and other.value == self.value

    def __hash__(self) -> int:
        return hash(self.value)


@dataclass
class LiquidLiteralInt(LiquidTerm):
    value: int
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __repr__(self):
        return f"{self.value}".lower()

    def __eq__(self, other):
        return isinstance(other, LiquidLiteralInt) and other.value == self.value

    def __hash__(self) -> int:
        return hash(self.value)


@dataclass
class LiquidLiteralFloat(LiquidTerm):
    value: float
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __repr__(self):
        return f"{self.value}".lower()

    def __eq__(self, other):
        return isinstance(other, LiquidLiteralFloat) and other.value == self.value

    def __hash__(self) -> int:
        return hash(self.value)


@dataclass
class LiquidLiteralString(LiquidTerm):
    value: str
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __repr__(self):
        return f"{self.value}".lower()

    def __eq__(self, other):
        return isinstance(other, LiquidLiteralString) and other.value == self.value

    def __hash__(self) -> int:
        return hash(self.value)


@dataclass
class LiquidVar(LiquidTerm):
    name: Name
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __repr__(self):
        return f"{self.name}"

    def __eq__(self, other):
        return type(other) is LiquidVar and other.name == self.name

    def __hash__(self) -> int:
        return hash(self.name)


@dataclass
class LiquidApp(LiquidTerm):
    fun: Name
    args: list[LiquidTerm]
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __repr__(self):
        if all(not c.isalnum() for c in self.fun.name) and len(self.args) == 2:
            (a1, a2) = (repr(x) for x in self.args)
            return f"({a1} {self.fun} {a2})"

        fargs = ",".join([repr(x) for x in self.args])
        return f"{self.fun}({fargs})"

    def __eq__(self, other):
        return (
            type(other) is LiquidApp and other.fun == self.fun and all(x == y for (x, y) in zip(self.args, other.args))
        )

    def __hash__(self) -> int:
        # Cache the structural hash: liquid terms are immutable after
        # construction, and substitution-built terms are DAGs with shared
        # subterms -- without memoization, hashing re-visits every path and is
        # exponential in the term's depth.
        h = getattr(self, "_hash", None)
        if h is None:
            h = hash(self.fun) + sum(hash(a) for a in self.args)
            object.__setattr__(self, "_hash", h)
        return h


def liquid_free_vars(e: LiquidTerm) -> list[Name]:
    if isinstance(e, LiquidVar):
        return [e.name]
    elif isinstance(e, LiquidApp):
        return [e.fun] + [x for arg in e.args for x in liquid_free_vars(arg)]
    else:
        return []
