"""Lean-style info view for the Aeon LSP.

Computes the information shown in the editor's "Aeon Info View" panel for a
cursor position: the inferred (refined) type of the expression under the
cursor, the goal type of a hole the cursor sits on, and the typing context
(locals and globals) in scope at that point — the same kind of contextual
panel Lean's infoview and LiquidJava's refinement view provide.

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

from aeon.core.types import Type
from aeon.lsp.completion import format_type
from aeon.typechecking.context import TypingContext, VariableBinder
from aeon.utils.name import Name

_HOLE_PATTERN = re.compile(r"\?([a-zA-Z_][a-zA-Z0-9_]*)")
_IDENTIFIER = re.compile(r"^[A-Za-z_][A-Za-z0-9_.]*$")


@dataclass(frozen=True)
class InfoEntry:
    """One ``name : type`` line of the context section."""

    name: str
    type: str


@dataclass(frozen=True)
class ExpressionInfo:
    """The tightest expression containing the cursor and its inferred type."""

    type: str
    range: tuple[int, int, int, int]  # 0-indexed (start line, start col, end line, end col)


@dataclass(frozen=True)
class GoalInfo:
    """A synthesis hole the cursor sits on: its name and goal (expected) type."""

    name: str
    type: str


@dataclass(frozen=True)
class InfoViewData:
    expression: Optional[ExpressionInfo] = None
    goal: Optional[GoalInfo] = None
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


def _dedup_innermost(vars_: list[tuple[Name, Type]]) -> list[tuple[Name, Type]]:
    """Keep the innermost binding per surface name, preserving binding order
    (``with_var`` appends, so the last occurrence shadows earlier ones)."""
    latest: dict[str, tuple[Name, Type]] = {}
    for name, ty in vars_:
        latest.pop(name.pretty(), None)
        latest[name.pretty()] = (name, ty)
    return list(latest.values())


def _entries_to_vars(entries) -> list[tuple[Name, Type]]:
    return [(e.name, e.type) for e in entries if isinstance(e, VariableBinder)]


def _to_info_entries(vars_: list[tuple[Name, Type]]) -> list[InfoEntry]:
    return [InfoEntry(name=n.pretty(), type=format_type(t)) for n, t in vars_]


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
    lambdas). Globals are filtered to plain identifiers — operator binders like
    ``+`` would only add noise."""
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
    globals_ = [e for e in _to_info_entries(global_vars) if _IDENTIFIER.match(e.name) and e.name not in local_names]
    return locals_, globals_


def _goal_for_hole(hole_name: str, typing_ctx, core) -> Optional[tuple[GoalInfo, Optional[TypingContext]]]:
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
            return GoalInfo(name=hole_name, type=format_type(ty)), ctx
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
    expression: Optional[ExpressionInfo] = None
    goal: Optional[GoalInfo] = None
    scope_ctx: Optional[TypingContext] = None

    if type_index is not None:
        scope_ctx = type_index.scope_at(line, character)
        result = type_index.type_at(line, character)
        if result is not None:
            ty, loc = result
            (sl, sc), (el, ec) = loc.get_start(), loc.get_end()
            expression = ExpressionInfo(
                type=format_type(ty),
                range=(max(sl - 1, 0), max(sc - 1, 0), max(el - 1, 0), max(ec - 1, 0)),
            )

    hole_name = _hole_at(source, line, character)
    if hole_name is not None and typing_ctx is not None and core is not None:
        found = _goal_for_hole(hole_name, typing_ctx, core)
        if found is not None:
            goal, hole_ctx = found
            # The hole's own context is the most faithful scope to display.
            if hole_ctx is not None:
                scope_ctx = hole_ctx
            # The polymorphic placeholder type the checker synthesises for a
            # bare hole is meaningless to the user; the goal supersedes it.
            expression = None

    locals_, globals_ = _split_scope(typing_ctx, scope_ctx, _top_level_names(core))
    return InfoViewData(expression=expression, goal=goal, locals=locals_, globals=globals_)
