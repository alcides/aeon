"""Structural LSP features over the core AST: document symbols, go-to-definition
and inlay hints.

All of these walk the elaborated core program (``driver.core``) once. Core node
ranges are 1-indexed; the plain dataclasses returned here keep that convention,
and the server converts to 0-indexed LSP positions in one place.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Iterator, Optional

from aeon.core.terms import Abstraction, Let, Rec, Term, TypeAbstraction, Var
from aeon.core.types import AbstractionType, RefinementPolymorphism, Type, TypePolymorphism
from aeon.utils.location import FileLocation
from aeon.utils.name import Name

# A core range, 1-indexed, end-exclusive: (start_line, start_col, end_line, end_col)
Span = tuple[int, int, int, int]


def _span(loc) -> Optional[Span]:
    if not isinstance(loc, FileLocation):
        return None
    (sl, sc), (el, ec) = loc.get_start(), loc.get_end()
    return (sl, sc, el, ec)


def iter_terms(t: Term) -> Iterator[Term]:
    """Yield ``t`` and every ``Term`` reachable from it (pre-order)."""
    import dataclasses
    from typing import Any, cast

    yield t
    if not dataclasses.is_dataclass(t):
        return
    for f in dataclasses.fields(cast(Any, t)):
        v = getattr(t, f.name)
        if isinstance(v, Term):
            yield from iter_terms(v)
        elif isinstance(v, (list, tuple)):
            for it in v:
                if isinstance(it, Term):
                    yield from iter_terms(it)


def _is_function_type(t: Type) -> bool:
    while isinstance(t, (TypePolymorphism, RefinementPolymorphism)):
        t = t.body
    return isinstance(t, AbstractionType)


def _name_range_after(source_lines: list[str], start_line: int, start_col: int, name: str) -> Optional[Span]:
    """Locate ``name`` as a whole word at/after the 1-indexed ``(start_line,
    start_col)`` and return its 1-indexed span. Used to point selection ranges
    and definitions at the bound identifier rather than the whole binding."""
    if not name:
        return None
    pattern = re.compile(r"(?<![A-Za-z0-9_.])" + re.escape(name) + r"(?![A-Za-z0-9_.])")
    li = start_line - 1
    col = start_col - 1
    # Search at most a handful of lines forward (binder names are near the keyword).
    for line_idx in range(li, min(li + 3, len(source_lines))):
        text = source_lines[line_idx]
        from_col = col if line_idx == li else 0
        m = pattern.search(text, from_col)
        if m:
            return (line_idx + 1, m.start() + 1, line_idx + 1, m.end() + 1)
    return None


# --------------------------------------------------------------------------- #
# Document symbols
# --------------------------------------------------------------------------- #


@dataclass(frozen=True)
class SymbolInfo:
    name: str
    detail: str
    is_function: bool
    full_range: Span
    selection_range: Span


def document_symbols(core: Term, source: str) -> list[SymbolInfo]:
    """Top-level definitions, in source order. Every ``def`` lowers to a ``Rec``
    on the outer spine whose ``body`` is the next definition; we walk that spine
    until the trailing expression (``main``)."""
    from aeon.lsp.completion import format_type

    lines = source.splitlines()
    out: list[SymbolInfo] = []
    cur: Term = core
    while isinstance(cur, Rec):
        full = _span(cur.loc)
        if full is not None:
            sel = _name_range_after(lines, full[0], full[1], cur.var_name.name) or full
            out.append(
                SymbolInfo(
                    name=cur.var_name.name,
                    detail=format_type(cur.var_type),
                    is_function=_is_function_type(cur.var_type),
                    full_range=full,
                    selection_range=sel,
                )
            )
        cur = cur.body
    return out


# --------------------------------------------------------------------------- #
# Go-to-definition
# --------------------------------------------------------------------------- #


@dataclass
class DefIndex:
    """Maps every variable *use* range to the *definition* range of its binder."""

    uses: list[tuple[Span, Name]]
    defs: dict[Name, Span]

    def definition_at(self, line0: int, char0: int) -> Optional[Span]:
        """The binder span for the use under the 0-indexed cursor, or ``None``."""
        pos = (line0 + 1, char0 + 1)
        best: Optional[tuple[Span, Name]] = None
        for span, name in self.uses:
            sl, sc, el, ec = span
            if (sl, sc) <= pos < (el, ec):
                if best is None or _span_size(span) <= _span_size(best[0]):
                    best = (span, name)
        if best is None:
            return None
        return self.defs.get(best[1])


def _span_size(s: Span) -> tuple[int, int]:
    return (s[2] - s[0], s[3] - s[1])


def build_def_index(core: Term, source: str) -> DefIndex:
    lines = source.splitlines()
    uses: list[tuple[Span, Name]] = []
    defs: dict[Name, Span] = {}
    for t in iter_terms(core):
        if isinstance(t, Var):
            sp = _span(t.loc)
            if sp is not None:
                uses.append((sp, t.name))
        elif isinstance(t, (Rec, Let)):
            sp = _span(t.loc)
            if sp is not None and t.var_name not in defs:
                defs[t.var_name] = _name_range_after(lines, sp[0], sp[1], t.var_name.name) or sp
        elif isinstance(t, Abstraction):
            sp = _span(t.loc)
            if sp is not None and t.var_name not in defs:
                # Parameter binder; point at the name if we can find it nearby.
                defs[t.var_name] = _name_range_after(lines, sp[0], sp[1], t.var_name.name) or sp
        elif isinstance(t, TypeAbstraction):
            sp = _span(t.loc)
            if sp is not None and t.name not in defs:
                defs[t.name] = sp
    return DefIndex(uses, defs)


# --------------------------------------------------------------------------- #
# Inlay hints (inferred types on un-annotated let bindings)
# --------------------------------------------------------------------------- #


@dataclass(frozen=True)
class InlayInfo:
    line: int  # 1-indexed, position to place the hint
    character: int  # 1-indexed
    label: str


def inlay_hints(core: Term, source: str, type_index) -> list[InlayInfo]:
    """Inferred-type hints for un-annotated ``let`` bindings.

    An annotated ``let x : T = …`` lowers to a ``Rec`` (the user already sees
    ``T``); only un-annotated bindings lower to ``Let``, and those are exactly
    where showing the inferred (refined) type is worth the screen space — e.g.
    ``let x = 41`` gets ``: {ν:Int | ν == 41}``."""
    from aeon.lsp.completion import format_type

    if type_index is None:
        return []
    lines = source.splitlines()
    out: list[InlayInfo] = []
    for t in iter_terms(core):
        if not isinstance(t, Let):
            continue
        binder = _span(t.loc)
        if binder is None:
            continue
        name_span = _name_range_after(lines, binder[0], binder[1], t.var_name.name)
        if name_span is None:
            continue
        vspan = _span(t.var_value.loc)
        if vspan is None:
            continue
        obs = type_index.obs_covering(vspan[0] - 1, vspan[1] - 1, vspan[3] - 1)
        if obs is None:
            continue
        out.append(
            InlayInfo(
                line=name_span[2],
                character=name_span[3],
                label=f": {format_type(obs.type)}",
            )
        )
    return out
