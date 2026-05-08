"""Multiplicities (Quantitative Type Theory).

Each binder in Aeon may carry a *multiplicity* drawn from a small semiring
``{0, 1, ω}`` that records how many times the bound name must be used
within its scope:

- ``M0``: erased — the name does not exist at run time. Useful for
  proof-only / ghost bindings that show up in refinements but never in
  the runtime term.
- ``M1``: linear — the name must be consumed exactly once. Passing a
  ``1``-bound value to a function that expects a ``1`` parameter
  transfers the obligation; passing it to an ``ω`` parameter is a type
  error.
- ``MOmega``: unrestricted — the name may be used any number of times,
  including zero. This is the default; existing programs that omit a
  multiplicity continue to behave identically.

This module only defines the algebra and the parser-facing tokens.
The linearity check that consumes these annotations lives in a later
phase; for now the type checker treats ``MOmega`` everywhere and the
new fields are inert.

The semiring laws (Atkey, *Syntax and Semantics of Quantitative Type
Theory*, LICS 2018):

- *Addition* combines the multiplicities of two uses in a single scope::

      0 + μ = μ + 0 = μ
      1 + 1 = ω
      1 + ω = ω + 1 = ω
      ω + ω = ω

- *Multiplication* combines the multiplicity of an outer binder with an
  inner one (e.g. multiplying the parameter's declared multiplicity by
  the argument's tally during application)::

      0 * μ = μ * 0 = 0
      1 * μ = μ * 1 = μ
      ω * 1 = ω = 1 * ω
      ω * ω = ω
"""

from __future__ import annotations

from enum import Enum


class Multiplicity(Enum):
    """The QTT multiplicity semiring ``{0, 1, ω}``."""

    M0 = "0"  # erased
    M1 = "1"  # linear (use exactly once)
    MOmega = "ω"  # unrestricted (use any number of times)

    def __repr__(self) -> str:
        return self.value

    def __str__(self) -> str:
        return self.value


M0 = Multiplicity.M0
M1 = Multiplicity.M1
MOmega = Multiplicity.MOmega


def add(a: Multiplicity, b: Multiplicity) -> Multiplicity:
    """Semiring addition — combine usage tallies in a single scope.

    ``0`` is the identity, ``1 + 1`` saturates to ``ω``, and ``ω`` is
    absorbing for any non-zero argument.
    """
    if a is M0:
        return b
    if b is M0:
        return a
    if a is MOmega or b is MOmega:
        return MOmega
    # both are M1
    return MOmega


def mul(a: Multiplicity, b: Multiplicity) -> Multiplicity:
    """Semiring multiplication — combine an outer multiplicity with an
    inner one (e.g. parameter multiplicity ⊗ argument tally during
    application).

    ``0`` is absorbing, ``1`` is the identity, and ``ω`` is absorbing
    for anything other than ``0``.
    """
    if a is M0 or b is M0:
        return M0
    if a is M1:
        return b
    if b is M1:
        return a
    return MOmega  # both are MOmega


def from_token(tok: str) -> Multiplicity:
    """Parse a surface-syntax multiplicity token (``"0"``, ``"1"``, or
    ``"omega"`` / ``"ω"``). Raises ``ValueError`` for anything else."""
    match tok:
        case "0":
            return M0
        case "1":
            return M1
        case "omega" | "ω":
            return MOmega
        case _:
            raise ValueError(f"Not a multiplicity token: {tok!r}")
