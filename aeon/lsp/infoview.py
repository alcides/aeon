"""Lean-style info view for the Aeon LSP.

Computes the information shown in the editor's "Aeon Info View" panel for a
cursor position: the typing context in scope (locals prominently, globals
collapsed) and the *target* — the goal type of a hole under the cursor, or
otherwise the inferred type of the expression under the cursor — rendered
turnstile-style (``⊢ T``) the way Lean's infoview and LiquidJava's refinement
view present a goal.

Each context entry is split into a base type and an optional refinement
predicate, so ``v:{k:Int | k > 0}`` is reported as ``v : Int`` with predicate
``v > 0`` — the refinement's bound variable is renamed to the *outer* binding
name and the predicate is pretty-printed (minimal parentheses). Anonymous and
compiler-internal binders (``_``, ``_cond``, ``_inner_…``) are hidden.

This module is deliberately free of any ``lsprotocol`` import so the logic is
unit-testable in isolation; the server serialises :class:`InfoViewData` to the
JSON payload of the custom ``aeon/infoView`` request.

All positions taken and returned by this module are **0-indexed** (LSP
convention); core source ranges are 1-indexed and converted internally.
"""

from __future__ import annotations

import re
from dataclasses import asdict, dataclass, field
from typing import Optional

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
from aeon.core.substitutions import substitution_in_liquid
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
    type_free_term_vars,
)
from aeon.lsp.completion import format_type
from aeon.typechecking.context import ReflectedBinder, TypingContext, UninterpretedBinder, VariableBinder
from aeon.utils.name import Name

_HOLE_PATTERN = re.compile(r"\?([a-zA-Z_][a-zA-Z0-9_]*)")

# Internal name ids render as superscript digits (``v⁴⁴⁸``); ``.pretty()`` drops
# them. This strips any that slip through a fallback rendering path so the user
# never sees a checker-internal id in a type, predicate or context entry.
_SUPERSCRIPT_DIGITS = str.maketrans("", "", "⁰¹²³⁴⁵⁶⁷⁸⁹")


def _strip_ids(s: str) -> str:
    return s.translate(_SUPERSCRIPT_DIGITS)


# Term-level binders that introduce a usable ``name : type`` value into scope.
# Type-level binders (``TypeBinder``/``TypeConstructorBinder``) are deliberately
# excluded — they bind types, not variables.
_VALUE_BINDERS = (VariableBinder, UninterpretedBinder, ReflectedBinder)

# Fallback refinement binder when there is no outer name to rename to (a goal or
# bare expression target), matching the convention used by ``format_type``.
_NU = Name("ν", 0)

# Precedence of the operators that appear in refinement predicates (higher binds
# tighter). Used by ``_pp_liquid`` to drop redundant parentheses.
_LIQUID_PREC = {
    "||": 1,
    "-->": 1,
    "&&": 2,
    "==": 3,
    "!=": 3,
    "<": 3,
    "<=": 3,
    ">": 3,
    ">=": 3,
    "+": 4,
    "-": 4,
    "*": 5,
    "/": 5,
    "%": 5,
}


@dataclass(frozen=True)
class InfoEntry:
    """One context line: ``name : type`` with an optional refinement predicate
    (already rendered with the outer name, e.g. ``("x", "Int", "x > 0")``)."""

    name: str
    type: str
    predicate: Optional[str] = None


@dataclass(frozen=True)
class TargetInfo:
    """The turnstile target: a hole's goal type, or the type of the expression
    under the cursor, split into base type and optional refinement predicate."""

    type: str
    predicate: Optional[str] = None


@dataclass(frozen=True)
class InfoViewData:
    target: Optional[TargetInfo] = None
    locals: list[InfoEntry] = field(default_factory=list)
    globals: list[InfoEntry] = field(default_factory=list)

    def to_dict(self) -> dict:
        """A JSON-serialisable payload for the ``aeon/infoView`` response."""
        return asdict(self)


def _hole_at(source: str, line: int, character: int) -> Optional[str]:
    """The name of the ``?hole`` token containing the 0-indexed cursor, or
    ``None``. The position just past the last character still counts, so the
    goal stays visible while the user types the hole name."""
    lines = source.splitlines()
    if not (0 <= line < len(lines)):
        return None
    for m in _HOLE_PATTERN.finditer(lines[line]):
        if m.start() <= character <= m.end():
            return m.group(1)
    return None


def _is_hidden(name: str) -> bool:
    """Anonymous (``_``) and compiler-internal (``_cond``, ``_self``,
    ``_inner_…``) binders are noise — hide them from the context."""
    return name.startswith("_")


def _is_operator(fun: str) -> bool:
    """Whether ``fun`` is a symbolic infix/prefix operator (``+``, ``&&``,
    ``-->``) rather than an alphanumeric function name (``Set_mem``)."""
    return bool(fun) and all(not c.isalnum() and c != "_" for c in fun)


def _pp_liquid(term: LiquidTerm, parent_prec: int = 0) -> str:
    """Pretty-print a refinement predicate with minimal parentheses, using
    surface (``pretty``) names so the user sees ``x > 0 && x < 10`` rather than
    the checker's ``((x⁷ > 0) && (x⁷ < 10))``."""
    if isinstance(term, LiquidVar):
        return term.name.pretty()
    if isinstance(term, LiquidLiteralBool):
        return "true" if term.value else "false"
    if isinstance(term, (LiquidLiteralInt, LiquidLiteralFloat)):
        return str(term.value)
    if isinstance(term, LiquidLiteralString):
        return '"' + str(term.value) + '"'
    if isinstance(term, LiquidLiteralUnit):
        return "()"
    if isinstance(term, LiquidApp):
        fun = term.fun.pretty()
        if _is_operator(fun) and len(term.args) == 2:
            prec = _LIQUID_PREC.get(fun, 0)
            left = _pp_liquid(term.args[0], prec)
            right = _pp_liquid(term.args[1], prec + 1)
            s = f"{left} {fun} {right}"
            return f"({s})" if prec < parent_prec else s
        if _is_operator(fun) and len(term.args) == 1:
            return f"{fun}{_pp_liquid(term.args[0], 100)}"
        args = ", ".join(_pp_liquid(a, 0) for a in term.args)
        return f"{fun}({args})"
    if isinstance(term, LiquidHornApplication):
        args = ", ".join(_pp_liquid(a, 0) for a, _ in term.argtypes)
        return f"{term.name.pretty()}({args})"
    if isinstance(term, LiquidHole):
        return "?"
    return _strip_ids(repr(term))


def _is_trivial(ref: LiquidTerm) -> bool:
    return isinstance(ref, LiquidLiteralBool) and ref.value is True


def _pp_type_atom(ty: Type) -> str:
    """Like :func:`_pp_type` but parenthesises compound types used as arguments."""
    inner = _pp_type(ty)
    if isinstance(ty, (AbstractionType, TypeConstructor)) and " " in inner:
        return f"({inner})"
    return inner


def _pp_type(ty: Type) -> str:
    """Pretty-print a full type id-free, rendering nested refinements with the
    minimal-parenthesis :func:`_pp_liquid` so every part — including globals'
    function types — reads cleanly (``∀a. a -> a -> Bool``, ``{ν:Int | ν > 0}``)
    rather than carrying the checker's internal name ids."""
    try:
        if isinstance(ty, Top):
            return "⊤"
        if isinstance(ty, TypeVar):
            return ty.name.pretty()
        if isinstance(ty, TypeConstructor):
            if not ty.args:
                return ty.name.pretty()
            return ty.name.pretty() + " " + " ".join(_pp_type_atom(a) for a in ty.args)
        if isinstance(ty, RefinedType):
            if _is_trivial(ty.refinement):
                return _pp_type(ty.type)
            pred = _pp_liquid(substitution_in_liquid(ty.refinement, LiquidVar(_NU), ty.name))
            return f"{{{_NU.pretty()}:{_pp_type(ty.type)} | {pred}}}"
        if isinstance(ty, AbstractionType):
            dom, cod = _pp_type(ty.var_type), _pp_type(ty.type)
            if ty.var_name in type_free_term_vars(ty.type):
                return f"({ty.var_name.pretty()}:{dom}) -> {cod}"
            return f"{dom} -> {cod}"
        if isinstance(ty, TypePolymorphism):
            return f"∀{ty.name.pretty()}. {_pp_type(ty.body)}"
        if isinstance(ty, RefinementPolymorphism):
            return f"∀<{ty.name.pretty()}:{_pp_type(ty.sort)}>. {_pp_type(ty.body)}"
        if isinstance(ty, ExistentialType):
            return _pp_type(ty.body)
        return _strip_ids(format_type(ty))
    except Exception:
        return _strip_ids(format_type(ty))


def _split_type(ty: Type, display_name: Optional[Name]) -> tuple[str, Optional[str]]:
    """Render ``ty`` as ``(base, predicate)``, both id-free.

    For a refined type the refinement's bound variable is renamed to
    ``display_name`` (the outer binding name) so ``v:{k:Int | k > 0}`` reads as
    ``v : Int`` with predicate ``v > 0``; an unrefined or trivially-true type
    has predicate ``None``. ``display_name`` of ``None`` (a goal or bare
    expression target with no outer name) falls back to ``ν``."""
    try:
        t = ty
        while isinstance(t, ExistentialType):
            t = t.body
        if isinstance(t, RefinedType) and not _is_trivial(t.refinement):
            repl = LiquidVar(display_name if display_name is not None else _NU)
            pred = substitution_in_liquid(t.refinement, repl, t.name)
            return _strip_ids(_pp_type(t.type)), _strip_ids(_pp_liquid(pred))
        if isinstance(t, RefinedType):
            return _strip_ids(_pp_type(t.type)), None
        return _strip_ids(_pp_type(t)), None
    except Exception:
        return _strip_ids(format_type(ty)), None


def _dedup_innermost(vars_: list[tuple[Name, Type]]) -> list[tuple[Name, Type]]:
    """Keep the innermost binding per surface name, preserving binding order
    (``with_var`` appends, so the last occurrence shadows earlier ones)."""
    latest: dict[str, tuple[Name, Type]] = {}
    for name, ty in vars_:
        latest.pop(name.pretty(), None)
        latest[name.pretty()] = (name, ty)
    return list(latest.values())


def _entries_to_vars(entries) -> list[tuple[Name, Type]]:
    """The value bindings of ``entries``, excluding anonymous/internal binders."""
    return [(e.name, e.type) for e in entries if isinstance(e, _VALUE_BINDERS) and not _is_hidden(e.name.pretty())]


def _to_info_entries(vars_: list[tuple[Name, Type]]) -> list[InfoEntry]:
    out: list[InfoEntry] = []
    for n, t in vars_:
        base, predicate = _split_type(t, n)
        out.append(InfoEntry(name=n.pretty(), type=base, predicate=predicate))
    return out


def _top_level_names(core) -> set[str]:
    """The names of the program's top-level definitions (the ``Rec`` spine)."""
    from aeon.core.terms import Rec

    names: set[str] = set()
    t = core
    while isinstance(t, Rec):
        names.add(t.var_name.pretty())
        t = t.body
    return names


def _split_scope(
    typing_ctx: Optional[TypingContext],
    scope_ctx: Optional[TypingContext],
    top_level: set[str],
) -> tuple[list[InfoEntry], list[InfoEntry]]:
    """Split the cursor's scope into (locals, globals).

    ``with_var`` builds contexts by appending to the prelude context, so the
    scope's entry list has the prelude as a prefix; everything after it was
    bound while checking — the program's top-level definitions (the ``Rec``
    spine, reported as globals) and the true locals (parameters, ``let``s,
    lambdas). Every in-scope value binding is reported, including operators and
    the rest of the prelude; the client keeps the globals section collapsed so
    the large builtin set stays out of the way. Anonymous and internal binders
    (``_``…) are dropped by :func:`_entries_to_vars`."""
    n_prelude = len(typing_ctx.entries) if typing_ctx is not None else 0
    if scope_ctx is None:
        scope_ctx = typing_ctx
    if scope_ctx is None:
        return [], []

    entries = scope_ctx.entries
    inner_entries = entries[n_prelude:] if len(entries) >= n_prelude else []
    prelude_entries = entries[:n_prelude] if len(entries) >= n_prelude else entries

    inner_vars = _dedup_innermost(_entries_to_vars(inner_entries))
    locals_ = _to_info_entries([(n, t) for n, t in inner_vars if n.pretty() not in top_level])
    local_names = {e.name for e in locals_}

    global_vars = _dedup_innermost(_entries_to_vars(prelude_entries)) + [
        (n, t) for n, t in inner_vars if n.pretty() in top_level
    ]
    globals_ = [e for e in _to_info_entries(global_vars) if e.name not in local_names]
    return locals_, globals_


def _goal_for_hole(hole_name: str, typing_ctx, core) -> Optional[tuple[Type, Optional[TypingContext]]]:
    """The goal type (and typing context) of the hole named ``hole_name``,
    recovered the same way the synthesiser sees it. Returns ``None`` when the
    hole cannot be typed (e.g. the last good core no longer contains it)."""
    try:
        from aeon.core.types import top
        from aeon.synthesis.identification import get_holes_info

        holes = get_holes_info(typing_ctx, core, top, [], refined_types=True)
    except Exception:
        return None
    for name, (ty, ctx) in holes.items():
        if name.pretty() == hole_name or name.name == hole_name:
            return ty, ctx
    return None


def compute_info_view(
    source: str,
    line: int,
    character: int,
    typing_ctx: Optional[TypingContext],
    type_index=None,
    core=None,
) -> InfoViewData:
    """Top-level entry: the info view contents for the 0-indexed cursor.

    ``type_index`` is the last successfully-built
    :class:`~aeon.lsp.typeindex.TypeIndex` for the document; ``typing_ctx`` is
    the top-level context and ``core`` the last good core program (both used to
    recover hole goals)."""
    target_ty: Optional[Type] = None
    scope_ctx: Optional[TypingContext] = None

    if type_index is not None:
        scope_ctx = type_index.scope_at(line, character)
        result = type_index.type_at(line, character)
        if result is not None:
            target_ty = result[0]

    hole_name = _hole_at(source, line, character)
    if hole_name is not None and typing_ctx is not None and core is not None:
        found = _goal_for_hole(hole_name, typing_ctx, core)
        if found is not None:
            goal_ty, hole_ctx = found
            # The goal supersedes the polymorphic placeholder the checker
            # synthesises for a bare hole, which is meaningless to the user.
            target_ty = goal_ty
            # The hole's own context is the most faithful scope to display.
            if hole_ctx is not None:
                scope_ctx = hole_ctx

    target: Optional[TargetInfo] = None
    if target_ty is not None:
        base, predicate = _split_type(target_ty, None)
        target = TargetInfo(type=base, predicate=predicate)

    locals_, globals_ = _split_scope(typing_ctx, scope_ctx, _top_level_names(core))
    return InfoViewData(target=target, locals=locals_, globals=globals_)
