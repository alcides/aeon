from __future__ import annotations

from typing import List
from typing import Tuple

from aeon.core.terms import Term
from aeon.core.types import Type


class Node:
    pass


class Expr(Node):
    pass


class TypeDecl(Node):
    name: str

    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return f"type {self.name};"


class Definition(Node):
    name: str
    args: list[tuple[str, Type]]
    type: Type
    body: Expr

    def __init__(self, name: str, args: list[tuple[str, Type]], type: Type,
                 body: Expr):
        self.name = name
        self.args = args
        self.type = type
        self.body = body

    def __repr__(self):
        if not self.args:
            return f"def {self.name} : {self.type} = {self.body};"
        else:
            args = ", ".join([f"{n}:{t}" for (n, t) in self.args])
            return f"def {self.name} ({args}) -> {self.type} {{\n {self.body} \n}}"


class Program(Node):
    type_decls: list[str]
    definitions: list[Definition]

    def __init__(self, td, defs):
        self.type_decls = td
        self.definitions = defs

    def __repr__(self):
        decls = "\n".join([str(td) for td in self.type_decls])
        defs = "\n".join([str(d) for d in self.definitions])
        return f"{decls}\n{defs}"
