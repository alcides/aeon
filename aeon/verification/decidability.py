"""Decidable-fragment classification for refinement predicates (issue #438).

Refinement checking is discharged by Z3. Liquid Types target a *decidable*
fragment — quantifier-free linear integer/real arithmetic (QF_LIA / QF_LRA),
the theory of equality with uninterpreted functions (EUF), plus the predicate
abstraction Horn solving adds on top. As long as every refinement stays inside
that fragment, Z3 is a *decision procedure*: it answers ``sat``/``unsat`` and
the type checker's yes/no verdict is reliable.

When a refinement steps outside the fragment — most commonly *nonlinear*
arithmetic such as ``x * y`` (a product of two unknowns), ``x / y`` or
``x % y`` with a non-constant divisor — Z3 becomes *incomplete*: it may return
``unknown`` or time out, and a once-passing program can start failing for no
visible reason. That is the worst failure mode for a verification-first
language, so this module classifies each predicate and lets the front end warn
(or, in strict mode, reject) before the solver is ever consulted.

What is *in* the fragment (no warning):

* Boolean/relational structure: ``&&``, ``||``, ``!``, ``-->``, ``==``,
  ``!=``, ``<``, ``<=``, ``>``, ``>=``, ``ite``.
* Linear arithmetic: ``+``, ``-``, and multiplication/division/modulo where at
  least one side is a *constant* (e.g. ``2 * x``, ``x / 4``, ``x % 2``).
* Uninterpreted-function applications (measures, datatype projections, reflected
  functions) and predicate-abstraction holes — these live in EUF / Horn.
* Set operations (``Set_mem``, ``Set_cup``, ...), which Z3 decides natively.

What is *out* of the fragment (warned about here):

* ``x * y`` — multiplication of two non-constant terms (nonlinear).
* ``x / y`` / ``x % y`` — division or modulo by a non-constant divisor.
* ``x ** y`` — exponentiation (no native Z3 theory). The surface syntax has no
  ``**`` operator, but the classifier flags it defensively.
* Quantifiers (``forall`` / ``exists``) inside a predicate. The surface
  refinement language cannot express these today; they are listed for
  completeness and flagged defensively if ever constructed.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from aeon.core.liquid import (
    LiquidApp,
    LiquidHole,
    LiquidLiteralBool,
    LiquidLiteralFloat,
    LiquidLiteralInt,
    LiquidLiteralString,
    LiquidLiteralUnit,
    LiquidTerm,
    LiquidVar,
)
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    Hole,
    If,
    ImplicitRefinementHole,
    Let,
    Literal,
    Rec,
    RefinementAbstraction,
    RefinementApplication,
    Term,
    TypeAbstraction,
    TypeApplication,
    Var,
)
from aeon.core.types import (
    AbstractionType,
    ExistentialType,
    LiquidHornApplication,
    RefinedType,
    RefinementPolymorphism,
    Top,
    Type,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
)
from aeon.utils.location import FileLocation, Location, SynthesizedLocation

# Operator names (the ``Name.name`` string of a ``LiquidApp.fun``).
_MULTIPLICATION = {"*", "*."}
_DIVISION_MODULO = {"/", "/.", "%", "%."}
_EXPONENTIATION = {"**", "^"}
_QUANTIFIERS = {"forall", "exists"}


@dataclass(frozen=True)
class DecidabilityWarning:
    """A refinement construct that leaves the decidable fragment Liquid Types
    target. ``construct`` names the offending syntax; ``message`` is a full,
    user-facing explanation; ``location`` points at the source span."""

    location: Location
    construct: str
    message: str

    def __str__(self) -> str:
        return f"{self.construct}: {self.message}"


def _mentions_variable(t: LiquidTerm) -> bool:
    """Whether ``t`` references any program variable (i.e. is *not* a constant).

    A term with no variable references folds to a literal and keeps a product /
    divisor inside linear arithmetic; one that mentions a variable does not.
    Predicate-abstraction holes and Horn applications count as variable-bearing.
    """
    match t:
        case LiquidVar(_):
            return True
        case (
            LiquidLiteralBool(_)
            | LiquidLiteralInt(_)
            | LiquidLiteralFloat(_)
            | LiquidLiteralString(_)
            | LiquidLiteralUnit()
        ):
            return False
        case LiquidApp(_, args, _):
            return any(_mentions_variable(a) for a in args)
        case LiquidHornApplication(_, _, _) | LiquidHole():
            return True
        case _:
            return False


def classify_refinement(refinement: LiquidTerm) -> list[DecidabilityWarning]:
    """Classify a single refinement predicate, returning a warning for every
    out-of-fragment construct it contains (depth-first, source order)."""
    warnings: list[DecidabilityWarning] = []
    _classify(refinement, warnings)
    return warnings


def _classify(t: LiquidTerm, warnings: list[DecidabilityWarning]) -> None:
    match t:
        case LiquidApp(fun, args, loc):
            name = fun.name
            if name in _MULTIPLICATION and len(args) == 2:
                if _mentions_variable(args[0]) and _mentions_variable(args[1]):
                    warnings.append(
                        DecidabilityWarning(
                            location=loc,
                            construct="nonlinear multiplication",
                            message=(
                                "multiplication of two non-constant terms (variable × variable) is nonlinear "
                                "arithmetic, which is outside the decidable fragment Liquid Types rely on; "
                                "Z3 may return 'unknown' or time out. Keep at least one factor constant, or "
                                "encode the relation with an uninterpreted function."
                            ),
                        )
                    )
            elif name in _DIVISION_MODULO and len(args) == 2:
                if _mentions_variable(args[1]):
                    op = "modulo" if name in ("%", "%.") else "division"
                    warnings.append(
                        DecidabilityWarning(
                            location=loc,
                            construct=f"non-constant {op}",
                            message=(
                                f"{op} by a non-constant divisor is nonlinear arithmetic, which is outside "
                                "the decidable fragment Liquid Types rely on; Z3 may return 'unknown' or time "
                                "out. Divide by a constant, or encode the relation with an uninterpreted function."
                            ),
                        )
                    )
            elif name in _EXPONENTIATION and len(args) == 2:
                warnings.append(
                    DecidabilityWarning(
                        location=loc,
                        construct="exponentiation",
                        message=(
                            "exponentiation has no native Z3 theory and is outside the decidable fragment "
                            "Liquid Types rely on; Z3 may return 'unknown' or time out."
                        ),
                    )
                )
            elif name in _QUANTIFIERS:
                warnings.append(
                    DecidabilityWarning(
                        location=loc,
                        construct="quantifier",
                        message=(
                            f"the quantifier '{name}' takes the predicate outside the quantifier-free "
                            "fragment Liquid Types rely on; Z3 may return 'unknown' or time out."
                        ),
                    )
                )
            for a in args:
                _classify(a, warnings)
        case _:
            # Literals, variables, Horn applications and holes carry no
            # out-of-fragment arithmetic of their own.
            pass


def _refinements_in_type(ty: Type, acc: list[LiquidTerm]) -> None:
    """Collect every refinement predicate reachable inside ``ty``."""
    match ty:
        case RefinedType(_, base, refinement):
            acc.append(refinement)
            _refinements_in_type(base, acc)
        case AbstractionType(_, var_type, rtype):
            _refinements_in_type(var_type, acc)
            _refinements_in_type(rtype, acc)
        case TypePolymorphism(_, _, body):
            _refinements_in_type(body, acc)
        case RefinementPolymorphism(_, sort, body):
            _refinements_in_type(sort, acc)
            _refinements_in_type(body, acc)
        case TypeConstructor(_, args):
            for arg in args:
                _refinements_in_type(arg, acc)
        case ExistentialType(binders, body):
            for _, bt in binders:
                _refinements_in_type(bt, acc)
            _refinements_in_type(body, acc)
        case Top() | TypeVar(_):
            pass
        case _:
            pass


def _types_in_term(term: Term, acc: list[Type]) -> None:
    """Collect every ``Type`` embedded inside a core ``term``."""
    match term:
        case Literal(_, ty, _):
            acc.append(ty)
        case Annotation(expr, ty, _):
            acc.append(ty)
            _types_in_term(expr, acc)
        case Application(fun, arg, _):
            _types_in_term(fun, acc)
            _types_in_term(arg, acc)
        case Abstraction(_, body, _):
            _types_in_term(body, acc)
        case Let(_, var_value, body, _, _):
            _types_in_term(var_value, acc)
            _types_in_term(body, acc)
        case Rec(var_type=var_type, var_value=var_value, body=body):
            acc.append(var_type)
            _types_in_term(var_value, acc)
            _types_in_term(body, acc)
        case If(cond, then, otherwise, _):
            _types_in_term(cond, acc)
            _types_in_term(then, acc)
            _types_in_term(otherwise, acc)
        case TypeAbstraction(_, _, body, _):
            _types_in_term(body, acc)
        case RefinementAbstraction(_, sort, body, _):
            acc.append(sort)
            _types_in_term(body, acc)
        case TypeApplication(body, ty, _):
            acc.append(ty)
            _types_in_term(body, acc)
        case RefinementApplication(body, refinement, _):
            _types_in_term(body, acc)
            _types_in_term(refinement, acc)
        case Var(_, _) | Hole(_, _) | ImplicitRefinementHole(_, _):
            pass
        case _:
            pass


def _location_in_file(loc: Location, source_path: str | None) -> bool:
    """Whether ``loc`` belongs to the user's source file.

    With ``source_path`` given, only refinements written in that file are kept,
    so warnings never point at library/prelude code spliced into the program.
    Synthesized locations (no real span) are always dropped.
    """
    if not isinstance(loc, FileLocation):
        return False
    if source_path is None:
        return True
    if loc.file == source_path:
        return True
    # The parser may record an unresolved path while the compiled unit stores
    # the resolved one (or vice versa); compare normalized paths so a relative
    # filename does not silently drop every warning.
    try:
        return Path(loc.file).resolve() == Path(source_path).resolve()
    except (OSError, ValueError):
        return False


def collect_decidability_warnings(
    term: Term,
    *,
    source_path: str | None = None,
) -> list[DecidabilityWarning]:
    """Scan a typed core ``term`` and return one warning per out-of-fragment
    refinement construct.

    Warnings are de-duplicated by ``(location span, construct)`` so a predicate
    that the pipeline copies (elaboration, ANF) is reported once, and restricted
    to ``source_path`` when given so only the user's own refinements warn.
    """
    types: list[Type] = []
    _types_in_term(term, types)

    refinements: list[LiquidTerm] = []
    for ty in types:
        _refinements_in_type(ty, refinements)

    seen: set[tuple[object, object, str]] = set()
    result: list[DecidabilityWarning] = []
    for refinement in refinements:
        for warning in classify_refinement(refinement):
            loc = warning.location
            if not _location_in_file(loc, source_path):
                continue
            key = (loc.get_start(), loc.get_end(), warning.construct)
            if key in seen:
                continue
            seen.add(key)
            result.append(warning)
    return result


def format_location(loc: Location) -> str:
    """Render a ``Location`` as ``file:line:col`` (or ``str`` when synthesized)."""
    if isinstance(loc, FileLocation):
        line, col = loc.start
        prefix = f"{loc.file}:" if loc.file else ""
        return f"{prefix}{line}:{col}"
    if isinstance(loc, SynthesizedLocation):
        return str(loc)
    return str(loc)
