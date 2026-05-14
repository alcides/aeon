"""LTA constraint language (Fig. 5 of the paper).

Atomic constraints over positions:
    ψa ::= true | false | p = p          (syntactic)
                       | p ⊨ p           (semantic, with optional substitution θ)

Composite constraints:
    ψ  ::= ψa | ¬ψ | ψ ∧ ψ | ψ ∨ ψ | θ.ψ

A Position is a sequence of integer indices or human-readable labels (e.g.
"in", "out", "type", "ref", "base"). The labels are interpreted by the
construction rules in `construction.py` — for example, a function-type
transition has incoming positions labelled "in" and "out".

A Substitution θ is a list of (target_pos, source_pos) pairs. Applying θ to a
constraint rewrites references to source_pos with references to target_pos.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Tuple, Sequence


Label = str | int


@dataclass(frozen=True)
class Position:
    """A path from the root of an LTA fragment to a sub-state or sub-transition.

    Concatenation is performed with the `/` operator: `Position(("type",)) / "ref"`.
    """

    path: Tuple[Label, ...] = ()

    def __truediv__(self, other: "Position | Label") -> "Position":
        if isinstance(other, Position):
            return Position(self.path + other.path)
        return Position(self.path + (other,))

    def __repr__(self) -> str:
        return ".".join(str(p) for p in self.path) if self.path else "ε"

    @staticmethod
    def root() -> "Position":
        return Position(())


@dataclass(frozen=True)
class Substitution:
    """A single position-substitution [target/source]: replace `source` by `target`."""

    target: Position
    source: Position

    def __repr__(self) -> str:
        return f"[{self.target}/{self.source}]"


# Atomic constraints --------------------------------------------------------


class Atom:
    """Base class for atomic constraints."""

    pass


@dataclass(frozen=True)
class ATrue(Atom):
    def __repr__(self) -> str:
        return "⊤"


@dataclass(frozen=True)
class AFalse(Atom):
    def __repr__(self) -> str:
        return "⊥"


@dataclass(frozen=True)
class AEq(Atom):
    """Syntactic equality between positions: p1 = p2."""

    p1: Position
    p2: Position

    def __repr__(self) -> str:
        return f"{self.p1} = {self.p2}"


@dataclass(frozen=True)
class AEntail(Atom):
    """Semantic entailment between positions, optionally under substitution θ: θ.p1 ⊨ p2."""

    p1: Position
    p2: Position
    theta: Tuple[Substitution, ...] = ()

    def __repr__(self) -> str:
        sub = "".join(repr(s) for s in self.theta)
        return f"{sub}{self.p1} ⊨ {self.p2}"


# Composite constraints -----------------------------------------------------


class Constraint:
    pass


@dataclass(frozen=True)
class CAtom(Constraint):
    atom: Atom

    def __repr__(self) -> str:
        return repr(self.atom)


@dataclass(frozen=True)
class CNot(Constraint):
    inner: Constraint

    def __repr__(self) -> str:
        return f"¬({self.inner})"


@dataclass(frozen=True)
class CAnd(Constraint):
    parts: Tuple[Constraint, ...]

    def __repr__(self) -> str:
        return " ∧ ".join(repr(p) for p in self.parts) if self.parts else "⊤"


@dataclass(frozen=True)
class COr(Constraint):
    parts: Tuple[Constraint, ...]

    def __repr__(self) -> str:
        return " ∨ ".join(repr(p) for p in self.parts) if self.parts else "⊥"


@dataclass(frozen=True)
class CSubst(Constraint):
    """θ.ψ — apply substitution θ to constraint ψ."""

    theta: Tuple[Substitution, ...]
    inner: Constraint

    def __repr__(self) -> str:
        sub = "".join(repr(s) for s in self.theta)
        return f"{sub}({self.inner})"


# Constructors / smart helpers ---------------------------------------------


CTRUE: Constraint = CAtom(ATrue())
CFALSE: Constraint = CAtom(AFalse())


def conj(*cs: Constraint) -> Constraint:
    flat: list[Constraint] = []
    for c in cs:
        if c is CTRUE:
            continue
        if c is CFALSE:
            return CFALSE
        if isinstance(c, CAnd):
            flat.extend(c.parts)
        else:
            flat.append(c)
    if not flat:
        return CTRUE
    if len(flat) == 1:
        return flat[0]
    return CAnd(tuple(flat))


def disj(*cs: Constraint) -> Constraint:
    flat: list[Constraint] = []
    for c in cs:
        if c is CFALSE:
            continue
        if c is CTRUE:
            return CTRUE
        if isinstance(c, COr):
            flat.extend(c.parts)
        else:
            flat.append(c)
    if not flat:
        return CFALSE
    if len(flat) == 1:
        return flat[0]
    return COr(tuple(flat))


def atoms_in(c: Constraint) -> list[Atom]:
    """Flatten a constraint into the list of atomic constraints it mentions
    (under top-level conjunction). Substitutions are pushed into atoms when
    they affect entailment."""
    out: list[Atom] = []

    def go(c: Constraint, theta: Sequence[Substitution]) -> None:
        if isinstance(c, CAtom):
            a = c.atom
            if isinstance(a, AEntail) and theta:
                out.append(AEntail(a.p1, a.p2, tuple(theta) + a.theta))
            else:
                out.append(a)
        elif isinstance(c, CAnd):
            for p in c.parts:
                go(p, theta)
        elif isinstance(c, CSubst):
            go(c.inner, tuple(theta) + c.theta)
        # CNot / COr are not decomposed here — caller can extend as needed.

    go(c, ())
    return out
