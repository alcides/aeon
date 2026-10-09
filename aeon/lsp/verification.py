"""Source-facing verification evidence for standard and custom LSP requests."""

from pathlib import Path
from urllib.parse import urlparse

from lsprotocol.types import Diagnostic, DiagnosticSeverity

from aeon.core.terms import Term, Var
from aeon.core.liquid import LiquidLiteralBool
from aeon.utils.location import FileLocation
from aeon.verification.helpers import constraint_goal, pretty_print_constraint
from aeon.verification.trace import VerificationResult, conjuncts, goal_location


def _document_uri(filename: str) -> str:
    return filename if urlparse(filename).scheme else Path(filename).resolve().as_uri()


def proof_obligations(results: list[VerificationResult], uri: str | None = None) -> list[dict]:
    from aeon.lsp.server import _loc_to_range
    from aeon.verification.smt import render_counterexample

    obligations: list[dict] = []
    seen: set[tuple[str, str, str]] = set()
    expanded: list[tuple[VerificationResult, bool]] = []
    for result in results:
        goals = [g for g in conjuncts(result.constraint) if constraint_goal(g) != LiquidLiteralBool(True)]
        if result.status == "valid" or len(goals) == 1:
            expanded.extend((VerificationResult(g, result.status, result.reason, result.cached), False) for g in goals)
        elif goals:
            # A failed conjunction must not be attached to its first expression:
            # that expression may be valid. Keep document-level evidence instead.
            expanded.append((result, True))
    for result, aggregate in expanded:
        if constraint_goal(result.constraint) == LiquidLiteralBool(True):
            continue
        loc = goal_location(result.constraint)
        if not isinstance(loc, FileLocation):
            continue
        if uri is not None and _document_uri(loc.file) != uri:
            continue
        text = pretty_print_constraint(result.constraint).translate(str.maketrans("", "", "⁰¹²³⁴⁵⁶⁷⁸⁹"))
        key = (text, str(loc), result.status)
        if key in seen:
            continue
        seen.add(key)
        span = None
        if not aggregate:
            r = _loc_to_range(loc)
            span = {
                "start": {"line": r.start.line, "character": r.start.character},
                "end": {"line": r.end.line, "character": r.end.character},
            }
        # Unknown/unsupported obligations have no falsifying model. Never
        # invent one or reinterpret failure-to-prove as a counterexample.
        counterexample = None
        if result.status == "invalid":
            try:
                counterexample = render_counterexample(result.constraint)
            except Exception:
                pass
        obligations.append(
            {
                "status": result.status,
                "obligation": text,
                "reason": result.reason,
                "counterexample": counterexample,
                "range": span,
                "cached": result.cached,
                "scope": "aggregate" if aggregate else "goal",
            }
        )
    return obligations


def obligations_at(obligations: list[dict], line: int, character: int) -> list[dict]:
    cursor = (line, character)
    return [
        p
        for p in obligations
        if p["range"] is not None
        and (p["range"]["start"]["line"], p["range"]["start"]["character"])
        <= cursor
        < (p["range"]["end"]["line"], p["range"]["end"]["character"])
    ]


def verification_markdown(obligations: list[dict]) -> str:
    sections = []
    for proof in obligations:
        text = f"Verification: **{proof['status']}**\n\n```text\n{proof['obligation']}\n```"
        if proof["reason"]:
            text += f"\n\nReason: {proof['reason']}"
        if proof["counterexample"]:
            text += f"\n\nCounterexample: `{proof['counterexample']}`"
        sections.append(text)
    return "\n\n".join(sections)


def runtime_warnings(core: Term | None, enabled: bool, uri: str | None = None) -> list[Diagnostic]:
    """Warn at native boundaries without evaluating the user's program."""
    from aeon.lsp.server import _loc_to_range

    out: list[Diagnostic] = []
    if core is None:
        return out
    stack = [core]
    seen: set[tuple[str, tuple[int, int]]] = set()
    while stack:
        term = stack.pop()
        if isinstance(term, Var) and term.name.pretty() == "native" and isinstance(term.loc, FileLocation):
            if uri is not None and _document_uri(term.loc.file) != uri:
                continue
            key = (term.loc.file, term.loc.start)
            if key not in seen:
                seen.add(key)
                mode = (
                    "Runtime verification is enabled; only executed refined calls are checked."
                    if enabled
                    else "Enable --runtime-verification to check refined arguments and results on executed calls."
                )
                out.append(
                    Diagnostic(
                        range=_loc_to_range(term.loc),
                        severity=DiagnosticSeverity.Warning,
                        source="aeon",
                        code="runtime-verification",
                        message=f"Native implementation is trusted, not statically verified. {mode}",
                        data={"kind": "runtime-verification", "enabled": enabled, "executed": False},
                    )
                )
        for child in vars(term).values():
            if isinstance(child, Term):
                stack.append(child)
    return out
