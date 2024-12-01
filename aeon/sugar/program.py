from __future__ import annotations

from dataclasses import dataclass
from dataclasses import field

from aeon.core.terms import Term
from aeon.core.types import Kind, Type
from aeon.typechecking.context import Polarity


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
    type_arguments: list[tuple[str, Kind, Polarity]]

    def __repr__(self):
        targs = ",".join(f"{t}:{k}" for (t, k, p) in self.type_arguments)
        return f"type {self.name} {targs};"


@dataclass
class Decorator(Node):
    name: str
    macro_args: list[Term]

    def __repr__(self):
        macro_args = ", ".join([f"{term}" for (term) in self.macro_args])
        return f"@{self.name}({macro_args})"


@dataclass
class Definition(Node):
    name: str
    args: list[tuple[str, Type]]
    type: Type
    body: Term  # TODO: replace with custom Sugar Expr
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
