from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

from aeon.core.terms import Term
from aeon.core.types import Kind, Type


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


class Polarity(Enum):
    NEITHER = 1
    POSITIVE = 2
    NEGATIVE = 3
    BOTH = 4


@dataclass
class TypeDecl(Node):
    name: str
    type_arguments: list[tuple[str, Kind, Polarity]]

    def __repr__(self):
        targs = ",".join(f"{t}:{k}" for (t, k, p) in self.type_arguments)
        return f"type {self.name} {targs};"


@dataclass
class Definition(Node):
    name: str
    args: list[tuple[str, Type]]
    type: Type
    body: Term  # TODO: replace with custom Sugar Expr

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
