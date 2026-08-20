"""Refinement-type-aware completion for the Aeon LSP.

This module is deliberately free of any ``lsprotocol`` import so the logic is
unit-testable in isolation; the server maps :class:`Completion` records to LSP
``CompletionItem``s.

Three tiers, increasing in sophistication (issue #27 gave the language the
``receiver.method`` dot syntax this targets):

* **Tier 1** — ``receiver.`` where the receiver is a literal (``1.``, ``"x".``)
  or a name in scope: list the methods defined on the receiver's base type. A
  method on type ``T`` is any in-scope binder named ``T.method`` (dotted
  definition) or ``T_method`` (a member imported from module ``T``); this is the
  exact convention ``ElaborationTypingContext.resolve_method`` dispatches on.
* **Tier 2** — the receiver is an arbitrary expression ``(f x).``; its type is
  recovered from the :class:`~aeon.lsp.typeindex.TypeIndex` by source range.
* **Tier 3** — *refinement-aware*: for each candidate whose receiver parameter
  is refined, an SMT subtyping check decides whether the receiver's known
  refinement satisfies the method's precondition. Infeasible candidates are
  de-ranked and annotated rather than hidden, and the precondition is surfaced.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Optional

from aeon.core.liquid import LiquidLiteralBool, LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import (
    AbstractionType,
    ExistentialType,
    RefinedType,
    RefinementPolymorphism,
    Top,
    Type,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
)
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

# --------------------------------------------------------------------------- #
# Completion records
# --------------------------------------------------------------------------- #

KIND_VARIABLE = "variable"
KIND_FUNCTION = "function"
KIND_METHOD = "method"


@dataclass(frozen=True)
class Completion:
    label: str
    detail: str
    kind: str
    insert_text: str
    sort_text: Optional[str] = None
    feasible: bool = True
    documentation: Optional[str] = None


# --------------------------------------------------------------------------- #
# Type formatting
# --------------------------------------------------------------------------- #

_CLEAN_BINDER = Name("ν", 0)


def format_type(t: Type) -> str:
    """A readable, refinement-preserving rendering of a core type.

    Trivial (``True``) refinements are dropped; a non-trivial refinement's bound
    variable is normalised to ``ν`` so the user sees ``{ν:Int | ν > 0}`` rather
    than the checker's internal ``v⁴⁴⁸``. Falls back to ``str`` for shapes the
    structural printer does not special-case."""
    try:
        return _fmt(t)
    except Exception:
        return str(t)


def _fmt(t: Type) -> str:
    match t:
        case Top():
            return "⊤"
        case TypeVar(name):
            return name.pretty()
        case TypeConstructor(name, args):
            if not args:
                return name.pretty()
            return f"{name.pretty()} " + " ".join(_fmt_atom(a) for a in args)
        case RefinedType(name, base, ref):
            if ref == LiquidLiteralBool(True):
                return _fmt(base)
            clean = substitution_in_liquid(ref, LiquidVar(_CLEAN_BINDER), name)
            return f"{{{_CLEAN_BINDER.pretty()}:{_fmt(base)} | {clean}}}"
        case AbstractionType(var_name, var_type, rtype):
            dom = _fmt(var_type)
            cod = _fmt(rtype)
            if _name_used_in(rtype, var_name):
                return f"({var_name.pretty()}:{dom}) -> {cod}"
            return f"{dom} -> {cod}"
        case TypePolymorphism(name, _, body):
            return f"∀{name.pretty()}. {_fmt(body)}"
        case RefinementPolymorphism(name, sort, body):
            return f"∀<{name.pretty()}:{_fmt(sort)}>. {_fmt(body)}"
        case ExistentialType(_, body):
            return _fmt(body)
        case _:
            return str(t)


def _fmt_atom(t: Type) -> str:
    """Like :func:`_fmt` but parenthesises compound types used as arguments."""
    inner = _fmt(t)
    if isinstance(t, (AbstractionType, TypeConstructor)) and " " in inner:
        return f"({inner})"
    return inner


def _name_used_in(t: Type, name: Name) -> bool:
    from aeon.core.types import type_free_term_vars

    try:
        return name in type_free_term_vars(t)
    except Exception:
        return False


# --------------------------------------------------------------------------- #
# Base-type extraction
# --------------------------------------------------------------------------- #


def base_type_name(t: Type) -> Optional[str]:
    """The name of ``t``'s underlying type constructor / variable — the
    namespace its methods live in — peeling refinements and existentials."""
    match t:
        case RefinedType(_, base, _):
            return base_type_name(base)
        case ExistentialType(_, body):
            return base_type_name(body)
        case TypeConstructor(name, _):
            return name.pretty()
        case TypeVar(name):
            return name.pretty()
        case _:
            return None


# --------------------------------------------------------------------------- #
# Receiver detection (textual)
# --------------------------------------------------------------------------- #

_WORD_RE = re.compile(r"[A-Za-z0-9_]")
_INT_RE = re.compile(r"^-?\d+$")
_FLOAT_RE = re.compile(r"^-?\d+\.\d+$")
_STRING_RE = re.compile(r'^".*"$')


@dataclass(frozen=True)
class DotContext:
    receiver_text: str
    receiver_start: int  # 0-indexed column where the receiver begins
    receiver_end: int  # 0-indexed column just past the receiver (the '.')
    prefix: str  # the partial method name already typed after the dot


def _is_word(c: str) -> bool:
    return bool(_WORD_RE.match(c))


def _scan_receiver_left(line: str, dot: int) -> Optional[int]:
    """Given the index of a ``.``, return the start column of the receiver
    expression immediately to its left, or ``None`` if there is none."""
    if dot <= 0:
        return None
    i = dot - 1
    c = line[i]
    if c == ")":
        depth = 0
        while i >= 0:
            if line[i] == ")":
                depth += 1
            elif line[i] == "(":
                depth -= 1
                if depth == 0:
                    return i
            i -= 1
        return None
    if c == '"':
        i -= 1
        while i >= 0:
            if line[i] == '"':
                return i
            i -= 1
        return None
    if _is_word(c) or c == ".":
        # A run of identifier characters and dots (covers `n`, `n.double`,
        # `Int`, `1`, `1.5`). Stop at whitespace or an operator/paren.
        while i >= 0 and (_is_word(line[i]) or line[i] == "."):
            i -= 1
        return i + 1
    return None


def parse_dot_context(line: str, character: int) -> Optional[DotContext]:
    """If the 0-indexed cursor sits in a ``receiver.<prefix>`` position, return
    its :class:`DotContext`; otherwise ``None``."""
    if character > len(line):
        character = len(line)
    j = character
    while j > 0 and _is_word(line[j - 1]):
        j -= 1
    prefix = line[j:character]
    if j == 0 or line[j - 1] != ".":
        return None
    dot = j - 1
    start = _scan_receiver_left(line, dot)
    if start is None or start == dot:
        return None
    return DotContext(
        receiver_text=line[start:dot],
        receiver_start=start,
        receiver_end=dot,
        prefix=prefix,
    )


def literal_base_type(text: str) -> Optional[str]:
    """The base type of a literal receiver, or ``None`` if ``text`` is not a
    recognised literal."""
    text = text.strip()
    if _FLOAT_RE.match(text):
        return "Float"
    if _INT_RE.match(text):
        return "Int"
    if _STRING_RE.match(text):
        return "String"
    if text in ("true", "false"):
        return "Bool"
    return None


def _is_simple_identifier(text: str) -> bool:
    return bool(text) and "." not in text and "(" not in text and not literal_base_type(text)


# --------------------------------------------------------------------------- #
# Method-type inspection (for Tier 3 receiver-parameter analysis)
# --------------------------------------------------------------------------- #


def method_receiver_param_type(method_type: Type, type_name: str) -> Optional[Type]:
    """The declared type of the parameter a ``receiver.method`` call fills.

    Mirrors elaboration's receiver placement: walk the arrow spine (skipping
    type-/refinement-polymorphism binders) and return the first explicit
    parameter whose base type matches ``type_name``. Instance-dictionary
    parameters carry a class type whose name will not match, so they are skipped
    naturally."""
    ty = method_type
    while True:
        match ty:
            case TypePolymorphism(_, _, body) | RefinementPolymorphism(_, _, body):
                ty = body
            case AbstractionType(_, var_type, rtype):
                if base_type_name(var_type) == type_name:
                    return var_type
                ty = rtype
            case _:
                return None


def _has_nontrivial_refinement(t: Type) -> bool:
    return isinstance(t, RefinedType) and t.refinement != LiquidLiteralBool(True)


def receiver_satisfies(ctx: TypingContext, receiver_type: Type, param_type: Type, loc) -> Optional[bool]:
    """Whether ``receiver_type`` is a subtype of the method's receiver parameter
    ``param_type`` (i.e. the receiver meets the method's precondition).

    Returns ``True``/``False`` when SMT decides it, or ``None`` when the question
    is not crisply decidable here (generic parameter, solver error) — callers
    treat ``None`` as "do not penalise"."""
    if not _has_nontrivial_refinement(param_type):
        return True
    try:
        from aeon.typechecking.entailment import entailment
        from aeon.verification.sub import sub
        from aeon.verification.vcs import LiquidConstraint

        constraint = sub(ctx, receiver_type, param_type, loc)
        if constraint == LiquidConstraint(LiquidLiteralBool(False)):
            return False
        return bool(entailment(ctx, constraint))
    except Exception:
        return None


# --------------------------------------------------------------------------- #
# Candidate enumeration
# --------------------------------------------------------------------------- #


def _dedup_latest(vars_: list[tuple[Name, Type]]) -> list[tuple[Name, Type]]:
    """Keep the innermost binding per surface name (``with_var`` appends, so the
    last occurrence shadows earlier ones)."""
    latest: dict[str, tuple[Name, Type]] = {}
    for name, ty in vars_:
        latest[name.pretty()] = (name, ty)
    return list(latest.values())


def _post_receiver_signature(method_type: Type, type_name: str) -> str:
    """The method's type with its receiver parameter removed — what the user
    still has to supply after ``receiver.method``."""
    removed = False
    parts: list[str] = []
    ty = method_type
    while isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
        ty = ty.body
    while isinstance(ty, AbstractionType):
        if not removed and base_type_name(ty.var_type) == type_name:
            removed = True
        else:
            parts.append(_fmt_atom(ty.var_type))
        ty = ty.type
    parts.append(format_type(ty))
    return " -> ".join(parts)


def method_completions(
    type_name: str,
    scope_vars: list[tuple[Name, Type]],
    *,
    receiver_obs=None,
    enable_feasibility: bool = True,
) -> list[Completion]:
    """All methods defined on ``type_name``, as completion records.

    When ``receiver_obs`` (a :class:`~aeon.lsp.typeindex.TypeObservation`) is
    given and ``enable_feasibility`` is set, each candidate is checked against
    the receiver's known refinement (Tier 3) and infeasible ones are de-ranked
    and annotated."""
    seen: set[str] = set()
    out: list[Completion] = []
    prefixes = (f"{type_name}.", f"{type_name}_")
    for name, ty in _dedup_latest(scope_vars):
        nm = name.name
        method: Optional[str] = None
        for p in prefixes:
            if nm.startswith(p) and len(nm) > len(p):
                method = nm[len(p) :]
                break
        if method is None or method in seen:
            continue
        seen.add(method)

        feasible = True
        documentation = format_type(ty)
        if enable_feasibility and receiver_obs is not None:
            param_type = method_receiver_param_type(ty, type_name)
            if param_type is not None and _has_nontrivial_refinement(param_type):
                verdict = receiver_satisfies(receiver_obs.ctx, receiver_obs.type, param_type, receiver_obs.loc)
                if verdict is False:
                    feasible = False
                    documentation = (
                        f"⚠ receiver may not satisfy precondition `{format_type(param_type)}`\n\n{documentation}"
                    )
                elif verdict is True:
                    documentation = f"✓ receiver satisfies `{format_type(param_type)}`\n\n{documentation}"

        # Feasible methods sort before infeasible ones; alphabetical within each.
        sort_rank = "1" if not feasible else "0"
        out.append(
            Completion(
                label=method,
                detail=_post_receiver_signature(ty, type_name),
                kind=KIND_METHOD,
                insert_text=method,
                sort_text=f"{sort_rank}{method}",
                feasible=feasible,
                documentation=documentation,
            )
        )
    return sorted(out, key=lambda c: c.sort_text or c.label)


def identifier_completions(scope_vars: list[tuple[Name, Type]]) -> list[Completion]:
    """Plain identifiers in scope (locals and globals), excluding the dotted
    method names that belong to dot completion."""
    out: list[Completion] = []
    for name, ty in _dedup_latest(scope_vars):
        label = name.pretty()
        if "." in name.name:
            continue
        kind = KIND_FUNCTION if isinstance(_strip_foralls(ty), AbstractionType) else KIND_VARIABLE
        out.append(
            Completion(
                label=label,
                detail=format_type(ty),
                kind=kind,
                insert_text=label,
                sort_text=label,
                documentation=format_type(ty),
            )
        )
    return sorted(out, key=lambda c: c.label)


def _strip_foralls(t: Type) -> Type:
    while isinstance(t, (TypePolymorphism, RefinementPolymorphism)):
        t = t.body
    return t


# --------------------------------------------------------------------------- #
# Orchestration
# --------------------------------------------------------------------------- #


def _literal_observation(text: str, ctx: TypingContext):
    """A synthetic :class:`TypeObservation` for a literal receiver, so Tier-3
    feasibility works for ``1.foo`` just as it does for variables."""
    from aeon.lsp.typeindex import TypeObservation
    from aeon.typechecking.typeinfer import (
        prim_litbool,
        prim_litfloat,
        prim_litint,
        prim_litstring,
    )
    from aeon.utils.location import SynthesizedLocation

    text = text.strip()
    try:
        if _FLOAT_RE.match(text):
            ty: Type = prim_litfloat(float(text))
        elif _INT_RE.match(text):
            ty = prim_litint(int(text))
        elif _STRING_RE.match(text):
            ty = prim_litstring(text[1:-1])
        elif text in ("true", "false"):
            ty = prim_litbool(text == "true")
        else:
            return None
    except Exception:
        return None
    # SynthesizedLocation is acceptable here: feasibility only reads the type and
    # context, and ``sub`` uses ``loc`` purely for error provenance.
    return TypeObservation(SynthesizedLocation("literal-receiver"), ctx, ty)


def _resolve_receiver(dot: DotContext, line: int, typing_ctx, type_index, scope_ctx, scope_vars):
    """Resolve the receiver to ``(base_type_name, receiver_observation)``.

    ``receiver_observation`` may be ``None`` when the type is known but no
    refinement context is available (then Tier-3 feasibility is skipped)."""
    text = dot.receiver_text
    lit = literal_base_type(text)
    if lit is not None:
        obs = _literal_observation(text, typing_ctx) if typing_ctx is not None else None
        return lit, obs
    if type_index is not None:
        obs = type_index.obs_covering(line, dot.receiver_start, dot.receiver_end)
        if obs is not None:
            bn = base_type_name(obs.type)
            if bn is not None:
                return bn, obs
    if _is_simple_identifier(text):
        # The receiver is a plain name the position index didn't cover (often
        # because the live, half-typed buffer no longer matches the last good
        # parse). Look the name up by string and synthesise an observation from
        # its declared type so Tier-3 feasibility still applies.
        from aeon.lsp.typeindex import TypeObservation
        from aeon.utils.location import SynthesizedLocation

        for name, ty in _dedup_latest(scope_vars):
            if name.pretty() == text:
                bn = base_type_name(ty)
                if bn is not None:
                    ctx = scope_ctx if scope_ctx is not None else typing_ctx
                    obs = TypeObservation(SynthesizedLocation("receiver-var"), ctx, ty) if ctx is not None else None
                    return bn, obs
    return None, None


def compute_completions(
    source: str,
    line: int,
    character: int,
    typing_ctx: Optional[TypingContext],
    type_index=None,
    *,
    enable_feasibility: bool = True,
) -> list[Completion]:
    """Top-level entry: completions for the 0-indexed cursor in ``source``.

    ``type_index`` is the last successfully-built
    :class:`~aeon.lsp.typeindex.TypeIndex` for the document (used for locals and
    receiver types); ``typing_ctx`` is the global fallback context."""
    lines = source.splitlines()
    line_text = lines[line] if 0 <= line < len(lines) else ""

    scope_ctx = None
    if type_index is not None:
        scope_ctx = type_index.scope_at(line, character)
    if scope_ctx is None:
        scope_ctx = typing_ctx
    scope_vars = scope_ctx.vars() if scope_ctx is not None else []

    dot = parse_dot_context(line_text, character)
    if dot is None:
        return identifier_completions(scope_vars)

    type_name, receiver_obs = _resolve_receiver(dot, line, typing_ctx, type_index, scope_ctx, scope_vars)
    if type_name is None:
        return []
    return method_completions(
        type_name,
        scope_vars,
        receiver_obs=receiver_obs,
        enable_feasibility=enable_feasibility,
    )
