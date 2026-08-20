"""Term hierarchy — re-export of the Rust core (``aeon-rs/src/terms.rs``)."""

from __future__ import annotations

import aeon.core.pickling  # noqa: F401  — registers pickle reducers for the Rust AST.

from aeon_rs import Abstraction as Abstraction
from aeon_rs import Annotation as Annotation
from aeon_rs import Application as Application
from aeon_rs import Hole as Hole
from aeon_rs import If as If
from aeon_rs import ImplicitRefinementHole as ImplicitRefinementHole
from aeon_rs import Let as Let
from aeon_rs import Literal as Literal
from aeon_rs import Rec as Rec
from aeon_rs import RefinementAbstraction as RefinementAbstraction
from aeon_rs import RefinementApplication as RefinementApplication
from aeon_rs import Term as Term
from aeon_rs import TypeAbstraction as TypeAbstraction
from aeon_rs import TypeApplication as TypeApplication
from aeon_rs import Var as Var

__all__ = [
    "Abstraction",
    "Annotation",
    "Application",
    "Hole",
    "If",
    "ImplicitRefinementHole",
    "Let",
    "Literal",
    "Rec",
    "RefinementAbstraction",
    "RefinementApplication",
    "Term",
    "TypeAbstraction",
    "TypeApplication",
    "Var",
]
