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

In addition to the QTT semiring there is a fourth, *non-semiring* marker:

- ``MN``: multiplicity-polymorphic — written ``(n x: T)`` in source.
  The function works for *any* concrete instantiation of the
  parameter's multiplicity. Caller-side, scaling by ``MN`` is the
  identity (the argument's tally flows through unchanged); body-side,
  the binder check is skipped (the body is trusted to be polymorphic).
  This is the *trust-the-user* flavour useful for prelude primitives
  like ``native`` and library helpers whose discipline is enforced
  elsewhere.

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

``MN`` short-circuits both: it is the identity in scaling and treats
addition the same as ``M1`` (one polymorphic use that callers
instantiate).
"""

from __future__ import annotations

from enum import Enum


class Multiplicity(Enum):
    """The QTT multiplicity semiring ``{0, 1, ω}`` plus the polymorphism
    marker ``MN``."""

    M0 = "0"  # erased
    M1 = "1"  # linear (use exactly once)
    MOmega = "ω"  # unrestricted (use any number of times)
    MN = "n"  # multiplicity-polymorphic (any concrete instantiation)

    def __repr__(self) -> str:
        return self.value

    def __str__(self) -> str:
        return self.value


M0 = Multiplicity.M0
M1 = Multiplicity.M1
MOmega = Multiplicity.MOmega
MN = Multiplicity.MN


def add(a: Multiplicity, b: Multiplicity) -> Multiplicity:
    """Semiring addition — combine usage tallies in a single scope.

    ``0`` is the identity, ``1 + 1`` saturates to ``ω``, and ``ω`` is
    absorbing for any non-zero argument. ``MN`` collapses to ``M1`` for
    the arithmetic.
    """
    if a is MN:
        a = M1
    if b is MN:
        b = M1
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

    ``0`` is absorbing, ``1`` is the identity, ``ω`` is absorbing for
    anything other than ``0``, and ``MN`` is the *identity* on the
    caller side — scaling by ``n`` preserves the argument's tally so
    a polymorphic-multiplicity function does not artificially constrain
    its callers.
    """
    if a is MN:
        return b
    if b is MN:
        return a
    if a is M0 or b is M0:
        return M0
    if a is M1:
        return b
    if b is M1:
        return a
    return MOmega  # both are MOmega


def from_token(tok: str) -> Multiplicity:
    """Parse a surface-syntax multiplicity token (``"0"``, ``"1"``,
    ``"omega"`` / ``"ω"``, or ``"n"``). Raises ``ValueError`` for
    anything else."""
    match tok:
        case "0":
            return M0
        case "1":
            return M1
        case "omega" | "ω":
            return MOmega
        case "n":
            return MN
        case _:
            raise ValueError(f"Not a multiplicity token: {tok!r}")
