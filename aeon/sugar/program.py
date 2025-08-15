from __future__ import annotations

from dataclasses import dataclass
from dataclasses import field

from aeon.utils.name import Name
from aeon.core.types import Kind
from aeon.sugar.stypes import SType, STypeConstructor

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


@dataclass(frozen=True)
class SRefinementAbstraction(STerm):
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


@dataclass(frozen=True)
class SRefinementApplication(STerm):
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
    rforalls: list[tuple[Name, Kind]]
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
            rforalls = " ".join([f"∀{n}:{k}" for (n, k) in self.rforalls])
            return f"def {self.name} {rforalls} {foralls} {args} : {self.type} {{\n {self.body} \n}}"


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


def get_term_vars(term: STerm) -> set[Name]:
    """Returns the set of variable names in the term."""
    match term:
        case SVar(name, _):
            return {name}
        case SLiteral(_, _):
            return set()
        case SAnnotation(expr, _):
            return get_term_vars(expr)
        case SHole(name, _):
            return {name}
        case SApplication(fun, arg, _):
            return get_term_vars(fun) | get_term_vars(arg)
        case SAbstraction(var_name, body, _):
            return {var_name} | get_term_vars(body)
        case SLet(var_name, var_value, body, _):
            return {var_name} | get_term_vars(var_value) | get_term_vars(body)
        case SRec(var_name, _, var_value, body, _):
            return {var_name} | get_term_vars(var_value) | get_term_vars(body)
        case SIf(cond, then, otherwise, _):
            return get_term_vars(cond) | get_term_vars(then) | get_term_vars(otherwise)
        case STypeAbstraction(name, _, body, _):
            return get_term_vars(body)
        case STypeApplication(body, _, _):
            return get_term_vars(body)
        case _:
            raise ValueError(f"Unknown term type: {type(term)}")
