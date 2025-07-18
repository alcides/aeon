from __future__ import annotations

from dataclasses import dataclass
from dataclasses import field

from aeon.utils.name import Name
from aeon.core.types import Kind
from aeon.sugar.stypes import SType, STypeConstructor, stype_pretty

from aeon.utils.location import Location, SynthesizedLocation


class STerm:
    loc: Location

    def __hash__(self) -> int:
        return str(self).__hash__()


@dataclass(frozen=True)
class SLiteral(STerm):
    value: object
    type: SType
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __repr__(self):
        if type(self.value) is str:
            return f'"{self.value}"'
        return f"{self.value}".lower()

    def __eq__(self, other):
        return isinstance(other, SLiteral) and self.value == other.value and self.type == other.type

    def __str__(self):
        if self.type == STypeConstructor(Name("String", 0)):
            return f'"{self.value}"'
        return f"{self.value}"


@dataclass(frozen=True)
class SVar(STerm):
    name: Name
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

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
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"({self.expr} : {self.type})"

    def __repr__(self):
        return f"({self.expr} : {self.type})"

    def __eq__(self, other):
        return isinstance(other, SAnnotation) and self.expr == other.expr


@dataclass(frozen=True)
class SHole(STerm):
    name: Name
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

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
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __repr__(self):
        return f"({self.fun} {self.arg})"

    def __eq__(self, other):
        return isinstance(other, SApplication) and self.fun == other.fun and self.arg == other.arg

    def __str__(self):
        return f"({self.fun} {self.arg})"


@dataclass(frozen=True)
class SAbstraction(STerm):
    var_name: Name
    body: STerm
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"(\\{self.var_name} -> {self.body})"

    def __eq__(self, other):
        return isinstance(other, SAbstraction) and self.var_name == other.var_name and self.body == other.body


@dataclass(frozen=True)
class SLet(STerm):
    var_name: Name
    var_value: STerm
    body: STerm
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

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
    var_name: Name
    var_type: SType
    var_value: STerm
    body: STerm
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
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

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
    name: Name
    kind: Kind
    body: STerm
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"ƛ{self.name}:{self.kind}.({self.body})"


@dataclass()  # frozen=True
class STypeApplication(STerm):
    body: STerm
    type: SType
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"({self.body})[{self.type}]"


class Node:
    pass


@dataclass
class ImportAe(Node):
    path: str
    func: str
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        if not self.func:
            return f"import {self.path};"
        else:
            return f"import {self.func} from {self.path};"


@dataclass
class TypeDecl(Node):
    name: Name
    args: list[Name] = field(default_factory=list)
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"type {self.name};"


@dataclass
class InductiveDecl(Node):
    name: Name
    args: list[Name] = field(default_factory=list)
    constructors: list[Definition] = field(default_factory=list)
    measures: list[Definition] = field(default_factory=list)
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __post_init__(self):
        assert isinstance(self.name, Name)

        for aname in self.args:
            assert isinstance(aname, Name)

    def __str__(self):
        args = " ".join(str(arg) for arg in self.args)
        constructors = " ".join(f"| {cons}" for (cons) in self.constructors)
        measures = " ".join(f"+ {dec}" for dec in self.measures)
        return f"inductive {self.name} {args} {constructors} {measures}"


@dataclass
class Decorator(Node):
    name: Name
    macro_args: list[STerm]
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __repr__(self):
        macro_args = ", ".join([f"{term}" for (term) in self.macro_args])
        return f"@{self.name}({macro_args})"


@dataclass
class Definition(Node):
    name: Name
    foralls: list[tuple[Name, Kind]]
    args: list[tuple[Name, SType]]
    type: SType
    body: STerm
    decorators: list[Decorator] = field(default_factory=list)
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __post_init__(self):
        assert isinstance(self.type, SType)

    def __str__(self):
        if not self.args:
            return f"def {self.name} : {self.type} = {self.body};"
        else:
            args = ", ".join([f"{n}:{t}" for (n, t) in self.args])
            foralls = " ".join([f"∀{n}:{k}" for (n, k) in self.foralls])
            return f"def {self.name} {foralls} {args} : {self.type} {{\n {self.body} \n}}"


@dataclass
class Program(Node):
    imports: list[ImportAe]
    type_decls: list[TypeDecl]
    inductive_decls: list[InductiveDecl]
    definitions: list[Definition]

    def __str__(self):
        imps = "\n".join([str(td) for td in self.imports])
        decls = "\n".join([str(td) for td in self.type_decls])
        inductives = "\n".join([str(td) for td in self.inductive_decls])
        defs = "\n".join([str(d) for d in self.definitions])
        return f"{imps}\n{decls}\n{inductives}\n{defs}"


def sterm_pretty(sterm: STerm) -> str:
    match sterm:
        case SLiteral(value=value, type=type):
            if type == STypeConstructor(Name("String", 0)):
                return f'"{value}"'
            return f"{value}"
        case SVar(name=name):
            return name.pretty()
        case SAnnotation(expr=expr, type=type):
            return f"({sterm_pretty(expr)} : {stype_pretty(type)})"
        case SHole(name=name):
            return f"?{name.pretty()}"
        case SApplication(fun=fun, arg=arg):
            return f"({sterm_pretty(fun)} {sterm_pretty(arg)})"
        case SAbstraction(var_name=var_name, body=body):
            return f"(\\{var_name.pretty()} -> {sterm_pretty(body)})"
        case SLet(var_name=var_name, var_value=var_value, body=body):
            return f"(let {var_name.pretty()} = {sterm_pretty(var_value)} in\n\t{sterm_pretty(body)})"
        case SRec(var_name=var_name, var_type=var_type, var_value=var_value, body=body):
            return "(let {} : {} = {} in\n\t{})".format(
                var_name.pretty(), stype_pretty(var_type), sterm_pretty(var_value), sterm_pretty(body)
            )
        case SIf(cond=cond, then=then, otherwise=otherwise):
            return f"(if {sterm_pretty(cond)} then {sterm_pretty(then)} else {sterm_pretty(otherwise)})"
        case STypeAbstraction(name=name, kind=kind, body=body):
            return f"ƛ{name.pretty()}:{kind}.({sterm_pretty(body)})"
        case STypeApplication(body=body, type=type):
            return f"({sterm_pretty(body)})[{stype_pretty(type)}]"
        case _:
            return str(sterm)
