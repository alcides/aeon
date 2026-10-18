"""Compiler-syntax inventory of term holes, distinct from predicate inference."""

from dataclasses import fields, is_dataclass

from aeon.sugar.parser import parse_main_program
from aeon.sugar.program import SHole, SLiteral
from aeon.sugar.stypes import SType


def term_hole_names(source: str, filename: str = "<inventory>") -> tuple[str, ...]:
    """Return distinct named expression holes from a parsed source file.

    Surface types contain refinement/predicate holes, not missing program
    expressions. Skip those type subtrees and all literal contents. Parse errors
    propagate so callers can retain an explicit audit outcome rather than
    silently considering malformed source hole-free.
    """
    program = parse_main_program(source, filename)
    names: set[str] = set()

    def visit(node):
        if isinstance(node, (SType, SLiteral)):
            return
        if isinstance(node, SHole):
            names.add(node.name.name)
        elif isinstance(node, (tuple, list)):
            for child in node:
                visit(child)
        elif isinstance(node, dict):
            for child in node.values():
                visit(child)
        elif is_dataclass(node):
            for field in fields(node):
                visit(getattr(node, field.name))

    visit(program)
    return tuple(sorted(names))
