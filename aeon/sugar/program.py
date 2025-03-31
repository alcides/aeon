from __future__ import annotations

from dataclasses import dataclass
from dataclasses import field

from aeon.core.types import Kind
from aeon.sugar.stypes import SType


class STerm:
    def __hash__(self) -> int:
        return str(self).__hash__()


@dataclass(frozen=True)
class SLiteral(STerm):
    value: object
    type: SType

    def __repr__(self):
        if type(self.value) is str:
            return f'"{self.value}"'
        return f"{self.value}".lower()

    def __eq__(self, other):
        return isinstance(other, SLiteral) and self.value == other.value and self.type == other.type


@dataclass(frozen=True)
class SVar(STerm):
    name: str

    def __str__(self):
        return f"{self.name}"

    def __repr__(self):
        return f"Var({self.name})"

    def __eq__(self, other):
        return isinstance(other, SVar) and self.name == other.name


@dataclass(frozen=True)
class SAnnotation(STerm):
    expr: STerm
    type: SType

    def __str__(self):
        return f"({self.expr} : {self.type})"

    def __repr__(self):
        return f"({self.expr} : {self.type})"

    def __eq__(self, other):
        return isinstance(other, SAnnotation) and self.expr == other.expr


@dataclass(frozen=True)
class SHole(STerm):
    name: str

    def __str__(self):
        return f"?{self.name}"

    def __repr__(self):
        return f"Hole({self.name})"

    def __eq__(self, other):
        return isinstance(other, SHole) and self.name == other.name


@dataclass(frozen=True)
class SApplication(STerm):
    fun: STerm
    arg: STerm

    def __repr__(self):
        return f"({self.fun} {self.arg})"

    def __eq__(self, other):
        return isinstance(other, SApplication) and self.fun == other.fun and self.arg == other.arg


@dataclass(frozen=True)
class SAbstraction(STerm):
    var_name: str
    body: STerm

    def __repr__(self):
        return f"(\\{self.var_name} -> {self.body})"

    def __eq__(self, other):
        return isinstance(other, SAbstraction) and self.var_name == other.var_name and self.body == other.body


@dataclass(frozen=True)
class SLet(STerm):
    var_name: str
    var_value: STerm
    body: STerm

    def __str__(self):
        return f"(let {self.var_name} = {self.var_value} in\n\t{self.body})"

    def __eq__(self, other):
        return (
            isinstance(other, SLet)
            and self.var_name == other.var_name
            and self.var_value == other.var_value
            and self.body == other.body
        )


@dataclass(frozen=True)
class SRec(STerm):
    var_name: str
    var_type: SType
    var_value: STerm
    body: STerm

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
            isinstance(other, SRec)
            and self.var_name == other.var_name
            and self.var_type == other.var_type
            and self.var_value == other.var_value
            and self.body == other.body
        )


@dataclass(frozen=True)
class SIf(STerm):
    cond: STerm
    then: STerm
    otherwise: STerm

    def __str__(self):
        return f"(if {self.cond} then {self.then} else {self.otherwise})"

    def __eq__(self, other):
        return (
            isinstance(other, SIf)
            and self.cond == other.cond
            and self.then == other.then
            and self.otherwise == other.otherwise
        )


@dataclass(frozen=True)
class STypeAbstraction(STerm):
    name: str
    kind: Kind
    body: STerm

    def __str__(self):
        return f"ƛ{self.name}:{self.kind}.({self.body})"


@dataclass()  # frozen=True
class STypeApplication(STerm):
    body: STerm
    type: SType

    def __init__(self, body, type):
        assert isinstance(body, STerm)
        self.body = body
        self.type = type

    def __str__(self):
        return f"({self.body})[{self.type}]"


class Node:
    pass


@dataclass
class ImportAe(Node):
    path: str
    func: str

    def __repr__(self):
        if not self.func:
            return f"import {self.path};"
        else:
            return f"import {self.func} from {self.path};"


@dataclass
class TypeDecl(Node):
    name: str
    args: list[str] = field(default_factory=list)

    def __repr__(self):
        return f"type {self.name};"


@dataclass
class Decorator(Node):
    name: str
    macro_args: list[STerm]

    def __repr__(self):
        macro_args = ", ".join([f"{term}" for (term) in self.macro_args])
        return f"@{self.name}({macro_args})"


@dataclass
class Definition(Node):
    name: str
    foralls: list[tuple[str, Kind]]
    args: list[tuple[str, SType]]
    type: SType
    body: STerm
    decorators: list[Decorator] = field(default_factory=list)

    def __repr__(self):
        if not self.args:
            return f"def {self.name} : {self.type} = {self.body};"
        else:
            args = ", ".join([f"{n}:{t}" for (n, t) in self.args])
            return f"def {self.name} {args} -> {self.type} {{\n {self.body} \n}}"


@dataclass
class Program(Node):
    imports: list[ImportAe]
    type_decls: list[TypeDecl]
    definitions: list[Definition]

    def __repr__(self):
        imps = "\n".join([str(td) for td in self.imports])
        decls = "\n".join([str(td) for td in self.type_decls])
        defs = "\n".join([str(d) for d in self.definitions])
        return f"{imps}\n{decls}\n{defs}"
