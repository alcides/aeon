from __future__ import annotations

from dataclasses import dataclass, field

from aeon.core.types import Kind
from aeon.core.types import t_string
from aeon.core.types import Type
from aeon.utils.location import Location, SynthesizedLocation
from aeon.utils.name import Name


class Term:
    loc: Location

    def __hash__(self) -> int:
        return str(self).__hash__()

    def pretty(self):
        pass


@dataclass(frozen=True)
class Literal(Term):
    value: object
    type: Type
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __repr__(self):
        if self.type == t_string:
            return f'"{self.value}"'
        return f"{self.value}".lower()

    def __eq__(self, other):
        return isinstance(other, Literal) and self.value == other.value and self.type == other.type

    def pretty(self):
        if self.type == t_string:
            return f'"{self.value}"'
        return f"{self.value}".lower()


@dataclass(frozen=True)
class Var(Term):
    name: Name
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"{self.name}"

    def __repr__(self):
        return f"Var({self.name})"

    def __eq__(self, other):
        return isinstance(other, Var) and self.name == other.name

    def pretty(self):
        return self.name.pretty()


@dataclass(frozen=True)
class Annotation(Term):
    expr: Term
    type: Type
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"({self.expr} : {self.type})"

    def __repr__(self):
        return f"({self.expr} : {self.type})"

    def __eq__(self, other):
        return isinstance(other, Annotation) and self.expr == other.expr

    def pretty(self):
        return f"({self.expr.pretty()} : {self.type})"


@dataclass(frozen=True)
class Hole(Term):
    name: Name
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"?{self.name}"

    def __repr__(self):
        return f"Hole({self.name})"

    def __eq__(self, other):
        return isinstance(other, Hole) and self.name == other.name

    def pretty(self):
        return f"?{self.name.pretty()}"


@dataclass(frozen=True)
class Application(Term):
    fun: Term
    arg: Term
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __repr__(self):
        return f"({self.fun} {self.arg})"

    def __eq__(self, other):
        return isinstance(other, Application) and self.fun == other.fun and self.arg == other.arg

    def pretty(self):
        return f"({self.fun.pretty()} {self.arg.pretty()})"


@dataclass(frozen=True)
class Abstraction(Term):
    var_name: Name
    body: Term
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __post_init__(self):
        assert isinstance(self.var_name, Name)

    def __repr__(self):
        return f"(\\{self.var_name} -> {self.body})"

    def __eq__(self, other):
        return isinstance(other, Abstraction) and self.var_name == other.var_name and self.body == other.body

    def pretty(self):
        return f"(\\{self.var_name.pretty()} -> {self.body.pretty()})"


@dataclass(frozen=True)
class Let(Term):
    var_name: Name
    var_value: Term
    body: Term
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"(let {self.var_name} = {self.var_value} in\n\t{self.body})"

    def __eq__(self, other):
        return (
            isinstance(other, Let)
            and self.var_name == other.var_name
            and self.var_value == other.var_value
            and self.body == other.body
        )

    def pretty(self):
        return f"(let {self.var_name.pretty()} = {self.var_value.pretty()} in\n\t{self.body.pretty()})"


@dataclass(frozen=True)
class Rec(Term):
    var_name: Name
    var_type: Type
    var_value: Term
    body: Term
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __repr__(self):
        return str(self)

    def __str__(self):
        return "(let {} : {} = {} in\n\t{})".format(
            self.var_name,
            self.var_type,
            self.var_value,
            self.body,
        )

    def __eq__(self, other):
        return (
            isinstance(other, Rec)
            and self.var_name == other.var_name
            and self.var_type == other.var_type
            and self.var_value == other.var_value
            and self.body == other.body
        )

    def pretty(self):
        return (
            f"(let {self.var_name.pretty()} : {self.var_type} = {self.var_value.pretty()} in\n\t{self.body.pretty()})"
        )


@dataclass(frozen=True)
class If(Term):
    cond: Term
    then: Term
    otherwise: Term
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"(if {self.cond} then {self.then} else {self.otherwise})"

    def __eq__(self, other):
        return (
            isinstance(other, If)
            and self.cond == other.cond
            and self.then == other.then
            and self.otherwise == other.otherwise
        )

    def pretty(self):
        return f"(if {self.cond.pretty()} then {self.then.pretty()} else {self.otherwise.pretty()})"


@dataclass(frozen=True)
class TypeAbstraction(Term):
    name: Name
    kind: Kind
    body: Term
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"ƛ{self.name}:{self.kind}.({self.body})"

    def pretty(self):
        return f"ƛ{self.name.pretty()}:{self.kind}.({self.body.pretty()})"


@dataclass(frozen=True)
class TypeApplication(Term):
    body: Term
    type: Type
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"({self.body})[{self.type}]"

    def pretty(self):
        return f"({self.body.pretty()})[{self.type}]"
