"""Position → type / scope index for the LSP.

The Aeon type checker has no typed AST: ``check_type_errors`` produces only
pass/fail plus verification conditions, and the driver exposes just the final
*top-level* typing context. That is enough to list globals, but not to answer
"what is the type of the expression under the cursor?" or "what is in scope
*here* (including ``let``/lambda locals)?" — the questions every good hover and
completion needs.

This module recovers that information without re-implementing the (subtle)
bidirectional context threading. The bidirectional checker's
``synth(ctx, term) -> (constraint, type)`` already computes the type of every
sub-expression with exactly the right context. We temporarily wrap ``synth`` so
that each call records ``(location, context, synthesized_type)``, run a checking
pass over the elaborated core program, and index the observations by source
range. The checker threads contexts correctly, so locals and shadowing fall out
for free; no SMT solving happens in ``synth``/``check`` (that is deferred to
entailment), so the extra pass is cheap.

Source ranges from core nodes are **1-indexed** (Lark ``meta.line``/``column``);
LSP positions are **0-indexed**. All public query methods take 0-indexed
``(line, character)`` and convert internally.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional

from aeon.core.types import Type
from aeon.typechecking.context import TypingContext
from aeon.utils.location import FileLocation, Location


@dataclass(frozen=True)
class TypeObservation:
    """One node's synthesized type and the context it was synthesized in."""

    loc: FileLocation
    ctx: TypingContext
    type: Type

    def start(self) -> tuple[int, int]:
        return self.loc.get_start()

    def end(self) -> tuple[int, int]:
        return self.loc.get_end()

    def span(self) -> tuple[int, int]:
        """A comparable size of the range: (line span, column span). Smaller is
        tighter, so the most specific enclosing node wins ties of containment."""
        (sl, sc), (el, ec) = self.start(), self.end()
        return (el - sl, ec - sc)


def _contains(obs: TypeObservation, line1: int, col1: int) -> bool:
    """Whether the (1-indexed) position ``(line1, col1)`` lies within ``obs``'s
    half-open range ``[start, end)`` under lexicographic ordering."""
    return obs.start() <= (line1, col1) < obs.end()


@dataclass
class TypeIndex:
    """Queryable index of per-node types and scopes for a single document."""

    observations: list[TypeObservation] = field(default_factory=list)

    def _tightest(self, line: int, character: int) -> Optional[TypeObservation]:
        """The smallest observation whose range contains the 0-indexed cursor.

        Ties (identical ranges, e.g. a variable synthesized more than once) are
        broken in favour of the *last* recorded observation, which carries the
        more refined "selfified" type the checker produces for variable uses."""
        line1, col1 = line + 1, character + 1
        best: Optional[TypeObservation] = None
        for obs in self.observations:
            if not _contains(obs, line1, col1):
                continue
            if best is None or obs.span() <= best.span():
                best = obs
        return best

    def type_at(self, line: int, character: int) -> Optional[tuple[Type, FileLocation]]:
        """The inferred type (and its source range) of the tightest expression
        containing the 0-indexed cursor, or ``None``."""
        obs = self._tightest(line, character)
        if obs is None:
            return None
        return (obs.type, obs.loc)

    def scope_at(self, line: int, character: int) -> Optional[TypingContext]:
        """The typing context (locals included) at the cursor, or ``None``."""
        obs = self._tightest(line, character)
        return obs.ctx if obs is not None else None

    def obs_covering(self, line: int, start_char: int, end_char: int) -> Optional[TypeObservation]:
        """The outermost observation fully contained in the 0-indexed span
        ``[start_char, end_char)`` on ``line`` — i.e. the type of the whole
        sub-expression occupying that span (a receiver before a ``.``). Returns
        the *largest* such observation so a parenthesised or chained receiver
        resolves to the type of the entire expression, not an inner fragment."""
        s = (line + 1, start_char + 1)
        e = (line + 1, end_char + 1)
        best: Optional[TypeObservation] = None
        for obs in self.observations:
            if obs.start() >= s and obs.end() <= e:
                if best is None or obs.span() >= best.span():
                    best = obs
        return best


def build_type_index(typing_ctx: TypingContext, core, expected: Optional[Type] = None) -> TypeIndex:
    """Build a :class:`TypeIndex` for ``core`` checked under ``typing_ctx``.

    Wraps ``aeon.typechecking.typeinfer.synth`` for the duration of one checking
    pass so every synthesized node is recorded. The wrapper delegates to the
    original ``synth`` (so recursion still flows through the wrapped global and
    every node is captured), and is always restored afterwards. A checking
    failure on an ill-typed program is swallowed — whatever was observed before
    the failure is still useful for tooling."""
    import aeon.typechecking.typeinfer as ti
    from aeon.core.types import top

    if expected is None:
        expected = top

    observations: list[TypeObservation] = []
    original_synth = ti.synth

    def recording_synth(ctx: TypingContext, t):
        result = original_synth(ctx, t)
        loc: Location = getattr(t, "loc", None)
        if isinstance(loc, FileLocation):
            observations.append(TypeObservation(loc, ctx, result[1]))
        return result

    ti.synth = recording_synth
    try:
        try:
            ti.check(typing_ctx, core, expected)
        except Exception:
            # Ill-typed (or partially typed) program: keep partial observations.
            pass
    finally:
        ti.synth = original_synth

    return TypeIndex(observations)
