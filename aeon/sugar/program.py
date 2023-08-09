from __future__ import annotations

from dataclasses import dataclass
from dataclasses import field

from aeon.core.terms import Term
from aeon.core.types import Type


class Node:
    pass


@dataclass
class ImportAe(Node):
    path: str
    func_or_type: str

    def __repr__(self):
        if not self.func_or_type:
            return f"import {self.path};"
        else:
            return f"import {self.func_or_type} from {self.path};"


@dataclass
class TypeDecl(Node):
    name: str

    def __repr__(self):
        return f"type {self.name};"


@dataclass
class Macro(Node):
    name: str
    expression: Term

    def __repr__(self):
        return f"@{self.name}({self.expression})"


@dataclass
class Definition(Node):
    name: str
    args: list[tuple[str, Type]]
    type: Type
    body: Term  # TODO: replace with custom Sugar Expr
    macros: list[Macro] = field(default_factory=list)

    def __repr__(self):
        if not self.args:
            return f"def {self.name} : {self.type} = {self.body};"
        else:
            args = ", ".join([f"{n}:{t}" for (n, t) in self.args])
            return f"def {self.name} ({args}) -> {self.type} {{\n {self.body} \n}}"


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
