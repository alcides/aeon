"""String-overloaded constraint-building helpers — used by tests only.

These bridge the (Python) lark parser into the Rust constraint builders,
so tests can pass strings like ``"a && b"`` directly. The pure-Rust
versions (``aeon_rs.imp`` / ``aeon_rs.end``) only accept already-parsed
``LiquidTerm`` instances; this module wraps them with a string overload.

Kept out of ``aeon.verification`` because the verification module is now
zero-Python (apart from re-exports). Tests can import these directly.
"""

from __future__ import annotations

from aeon_rs import end as _rs_end
from aeon_rs import imp as _rs_imp

from aeon.core.liquid import LiquidTerm
from aeon.core.parser import parse_term
from aeon.core.substitutions import liquefy
from aeon.verification.vcs import Constraint, LiquidConstraint


def parse_liquid(t: str) -> LiquidTerm | None:
    """Parse a string into a `LiquidTerm` via the core parser + liquefy."""
    tp = parse_term(t)
    return liquefy(tp)


def imp(a: str | LiquidTerm, b: Constraint) -> Constraint:
    """Build an `Implication` whose pred is `a` (or `parse_liquid(a)`)."""
    e: LiquidTerm | None = a if isinstance(a, LiquidTerm) else parse_liquid(a)
    assert e is not None
    return _rs_imp(e, b)


def end(a: str | LiquidTerm) -> LiquidConstraint:
    """Wrap `a` (or `parse_liquid(a)`) in a `LiquidConstraint`."""
    e: LiquidTerm | None = a if isinstance(a, LiquidTerm) else parse_liquid(a)
    assert e is not None
    return _rs_end(e)
