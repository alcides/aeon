from __future__ import annotations

from dataclasses import dataclass

from aeon.core.terms import Term
from aeon.core.types import Type


class Node:
    pass


@dataclass
class TypeDecl(Node):
    name: str

    def __repr__(self):
        return f"type {self.name};"


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
    type_decls: list[TypeDecl]
    definitions: list[Definition]

    def __repr__(self):
        decls = "\n".join([str(td) for td in self.type_decls])
        defs = "\n".join([str(d) for d in self.definitions])
        return f"{decls}\n{defs}"
