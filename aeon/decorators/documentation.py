"""Documentation shared by HTML generation and synthesis."""

from aeon.decorators.api import Metadata, metadata_update
from aeon.errors import InvalidDecoratorArgumentError
from aeon.sugar.program import Decorator, Definition, SLiteral


def doc_text(decorator: Decorator) -> str:
    """Read the literal documentation without evaluating Aeon code."""
    if len(decorator.macro_args) == 1:
        arg = decorator.macro_args[0]
        if isinstance(arg, SLiteral) and isinstance(arg.value, str):
            return arg.value
    raise InvalidDecoratorArgumentError(decorator, "expected exactly one string literal")


def doc(decorator: Decorator, fun: Definition, metadata: Metadata) -> tuple[Definition, list[Definition], Metadata]:
    return fun, [], metadata_update(metadata, fun, {"doc": doc_text(decorator)})
