"""Decorator API types and helpers — re-exports the Rust core for
``metadata_update`` / ``metadata_update_by_name`` /
``CORE_DECORATOR_QUEUE_META_KEY``. The ``Metadata`` / ``DecoratorType`` /
``CoreDecoratorType`` aliases stay in Python (they're purely structural)."""

from __future__ import annotations

from typing import Any, Callable, TYPE_CHECKING

from aeon.utils.name import Name
from aeon.sugar.program import Definition, Decorator

from aeon_rs import (
    CORE_DECORATOR_QUEUE_META_KEY,
    metadata_update,
    metadata_update_by_name,
)

if TYPE_CHECKING:
    from aeon.core.terms import Term
    from aeon.typechecking.context import TypingContext

Metadata = dict[Name, Any]
DecoratorType = Callable[[Decorator, Definition, Metadata], tuple[Definition, list[Definition], Metadata]]
CoreDecoratorType = Callable[[Decorator, Name, "TypingContext", "Term", Metadata], Metadata]

__all__ = [
    "CORE_DECORATOR_QUEUE_META_KEY",
    "CoreDecoratorType",
    "DecoratorType",
    "Metadata",
    "metadata_update",
    "metadata_update_by_name",
]
