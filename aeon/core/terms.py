from __future__ import annotations

from dataclasses import dataclass

from aeon.core.types import Kind
from aeon.core.types import t_string
from aeon.core.types import Type


class Term:
    def __hash__(self) -> int:
        return str(self).__hash__()


class Literal(Term):
    value: object
    type: Type

    def __init__(self, value, type: Type):
        self.value = value
        self.type = type

    def __repr__(self):
        if self.type == t_string:
            return f'"{self.value}"'
        return f"{self.value}".lower()

    def __eq__(self, other):
        return isinstance(other, Literal) and self.value == other.value and self.type == other.type


class Var(Term):
    name: str

    def __init__(self, name: str):
        self.name = name

    def __str__(self):
        return f"{self.name}"

    def __repr__(self):
        return f"Var({self.name})"

    def __eq__(self, other):
        return isinstance(other, Var) and self.name == other.name


class Annotation(Term):
    expr: Term
    type: Type

    def __init__(self, expr: Term, type: Type):
        self.expr = expr
        self.type = type

    def __str__(self):
        return f"({self.expr} : {self.type})"

    def __repr__(self):
        return f"({self.expr} : {self.type})"

    def __eq__(self, other):
        return isinstance(other, Annotation) and self.expr == other.expr


class Hole(Term):
    name: str

    def __init__(self, name: str):
        self.name = name

    def __str__(self):
        return f"?{self.name}"

    def __repr__(self):
        return f"Hole({self.name})"

    def __eq__(self, other):
        return isinstance(other, Hole) and self.name == other.name


class Application(Term):
    fun: Term
    arg: Term

    def __init__(self, fun: Term, arg: Term):
        self.fun = fun
        self.arg = arg

    def __repr__(self):
        return f"({self.fun} {self.arg})"

    def __eq__(self, other):
        return isinstance(other, Application) and self.fun == other.fun and self.arg == other.arg


class Abstraction(Term):
    var_name: str
    body: Term

    def __init__(self, var_name: str, body: Term):
        self.var_name = var_name
        self.body = body

    def __repr__(self):
        return f"(\\{self.var_name} -> {self.body})"

    def __eq__(self, other):
        return isinstance(other, Abstraction) and self.var_name == other.var_name and self.body == other.body


class Let(Term):
    var_name: str
    var_value: Term
    body: Term

    def __init__(self, var_name: str, var_value: Term, body: Term):
        self.var_name = var_name
        self.var_value = var_value
        self.body = body

    def __str__(self):
        return f"(let {self.var_name} = {self.var_value} in\n\t{self.body})"

    def __eq__(self, other):
        return (
            isinstance(other, Let)
            and self.var_name == other.var_name
            and self.var_value == other.var_value
            and self.body == other.body
        )


class Rec(Term):
    var_name: str
    var_type: Type
    var_value: Term
    body: Term

    def __init__(self, var_name: str, var_type: Type, var_value: Term, body: Term):
        self.var_name = var_name
        self.var_type = var_type
        self.var_value = var_value
        self.body = body

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


class If(Term):
    cond: Term
    then: Term
    otherwise: Term

    def __init__(self, cond: Term, then: Term, otherwise: Term):
        self.cond = cond
        self.then = then
        self.otherwise = otherwise

    def __str__(self):
        return f"(if {self.cond} then {self.then} else {self.otherwise})"

    def __eq__(self, other):
        return (
            isinstance(other, If)
            and self.cond == other.cond
            and self.then == other.then
            and self.otherwise == other.otherwise
        )


@dataclass
class TypeAbstraction(Term):
    name: str
    kind: Kind
    body: Term

    def __str__(self):
        return f"ƛ{self.name}:{self.kind}.({self.body})"


@dataclass
class TypeApplication(Term):
    body: Term
    type: Type

    def __str__(self):
        return f"({self.body})[{self.type}]"
