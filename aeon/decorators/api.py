"""Decorator API types and helpers — re-export of the Rust core
(``aeon-rs/src/decorators.rs``).

The two type aliases ``Metadata`` and ``DecoratorType`` /
``CoreDecoratorType`` stay in Python because they're purely structural
type annotations.
"""

from __future__ import annotations

from typing import Any, Callable, TYPE_CHECKING

from aeon.utils.name import Name
from aeon.sugar.program import Decorator, Definition

from aeon_rs import (
    CORE_DECORATOR_QUEUE_META_KEY as CORE_DECORATOR_QUEUE_META_KEY,
)
from aeon_rs import metadata_update as metadata_update
from aeon_rs import metadata_update_by_name as metadata_update_by_name

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
