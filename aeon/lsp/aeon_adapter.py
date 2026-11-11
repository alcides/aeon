# This module contain modified code from zc.buildout http://www.buildout.org/en/latest/
# which has this copyright
##############################################################################
#
# Copyright (c) 2005-2009 Zope Foundation and Contributors.
# All Rights Reserved.
#
# This software is subject to the provisions of the Zope Public License,
# Version 2.1 (ZPL).  A copy of the ZPL should accompany this distribution.
# THIS SOFTWARE IS PROVIDED "AS IS" AND ANY AND ALL EXPRESS OR IMPLIED
# WARRANTIES ARE DISCLAIMED, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
# WARRANTIES OF TITLE, MERCHANTABILITY, AGAINST INFRINGEMENT, AND FITNESS
# FOR A PARTICULAR PURPOSE.
#
##############################################################################

import io
import asyncio
import logging
import re
import urllib.parse
from dataclasses import dataclass, field
from copy import deepcopy
from pathlib import Path
from typing import Dict, List, TextIO, cast

import requests
from lark.exceptions import UnexpectedCharacters, UnexpectedInput, UnexpectedToken
from lsprotocol.types import Diagnostic, DiagnosticSeverity
from lsprotocol.types import Position, Range

from z3.z3types import Z3Exception

from aeon.facade.driver import AeonDriver
from aeon.core.terms import Term
from aeon.decorators.api import Metadata
from aeon.lsp.server import AeonLanguageServer, _loc_to_range
from aeon.lsp.z3_errors import z3_diagnostic_message
from aeon.typechecking.context import TypingContext

requests_session = requests.Session()

logger = logging.getLogger(__name__)

URI = str
HTTP_SCHEMES = {"http", "https"}

_HOLE_PATTERN = re.compile(r"\?([a-zA-Z_][a-zA-Z0-9_]*)")


@dataclass(frozen=True)
class HolePosition:
    name: str
    range: Range


@dataclass(frozen=True)
class ParseResult:
    diagnostics: List[Diagnostic]
    holes: List[HolePosition] = field(default_factory=list)


# Last-good per-document analysis state, used by the type-aware features (hover,
# completion, inlay hints, navigation). Kept separate from the parse cache and
# only overwritten on a parse that reaches core generation, so these survive
# transient errors while the user is mid-edit — exactly when completion is most
# wanted. Values are plain objects to avoid importing core types here.
_type_index_cache: "Dict[URI, object]" = {}
_typing_ctx_cache: "Dict[URI, object]" = {}
_core_cache: "Dict[URI, object]" = {}
_metadata_cache: "Dict[URI, object]" = {}
_evaluation_ctx_cache: "Dict[URI, object]" = {}
_constructor_names_cache: "Dict[URI, object]" = {}
_constructor_registry_cache: "Dict[URI, object]" = {}
# Structured semantic errors from the most recent parse of each document. Unlike
# the caches above these track the *current* parse (cleared on every reparse) so
# the info view's error tab can present the live verification failures — their
# counterexamples and the simplification chain of the failing VC.
_errors_cache: "Dict[URI, list]" = {}
_proof_cache: "Dict[URI, list[dict]]" = {}
_dependencies: dict[URI, set[URI]] = {}
_revision = 0
_changed_at: dict[URI, int] = {}
_parse_sources: dict[URI, str] = {}
_pending: dict[URI, tuple[str, int, asyncio.Task]] = {}


def analysis_caches() -> dict[str, dict]:
    """Serializable editor state, excluding compiler sessions and solvers."""
    return {
        "index": _type_index_cache,
        "context": _typing_ctx_cache,
        "core": _core_cache,
        "metadata": _metadata_cache,
        "evaluation": _evaluation_ctx_cache,
        "constructors": _constructor_names_cache,
        "constructor_registry": _constructor_registry_cache,
        "errors": _errors_cache,
        "proofs": _proof_cache,
    }


def get_proof_obligations(uri: URI) -> list[dict]:
    """Evidence from the current verification pass, never last-good evidence."""
    return _proof_cache.get(uri, [])


def get_type_index(uri: URI):
    """The last successfully-built ``TypeIndex`` for ``uri`` (or ``None``)."""
    return _type_index_cache.get(uri)


def get_typing_ctx(uri: URI):
    """The last successful top-level typing context for ``uri`` (or ``None``)."""
    return _typing_ctx_cache.get(uri)


def get_core(uri: URI):
    """The last successfully-generated core program for ``uri`` (or ``None``)."""
    return _core_cache.get(uri)


def get_metadata(uri: URI):
    """The metadata from the last parse of ``uri`` that reached core generation."""
    return _metadata_cache.get(uri)


def cache_driver_analysis(driver: AeonDriver, uri: URI) -> None:
    """Snapshot ``driver``'s analysis fields for ``uri`` (LSP feature cache)."""
    _refresh_analysis(driver, uri)


def restore_driver_from_cache(driver: AeonDriver, uri: URI) -> bool:
    """Repopulate ``driver`` analysis fields from the last good parse of ``uri``.

    Used when a fresh parse aborts with :class:`Z3Exception` but an earlier
    successful parse left enough state to run synthesis or type-aware features.
    """
    core = _core_cache.get(uri)
    typing_ctx = _typing_ctx_cache.get(uri)
    metadata = _metadata_cache.get(uri)
    if core is None or typing_ctx is None or metadata is None:
        return False
    driver.core = cast(Term, core)
    driver.typing_ctx = cast(TypingContext, typing_ctx)
    driver.metadata = cast(Metadata, metadata)
    constructor_names = _constructor_names_cache.get(uri)
    driver.constructor_names = set(cast(set[str], constructor_names or set()))
    from aeon.verification.constructor_registry import ConstructorRegistry
    from dataclasses import fields

    cached_registry = _constructor_registry_cache.get(uri)
    if cached_registry is not None:
        registry = driver.session.state(ConstructorRegistry)
        for item in fields(ConstructorRegistry):
            setattr(registry, item.name, deepcopy(getattr(cached_registry, item.name)))
    # Check-only workers deliberately never serialize LLVM engines or runtime
    # closures. Rebuild them in the requesting driver's own session instead.
    driver.prepare_execution()
    return True


def get_errors(uri: URI) -> list:
    """The structured semantic errors (``AeonError``) of ``uri``'s last parse."""
    return _errors_cache.get(uri, [])


def driver_dependencies(driver: AeonDriver) -> set[URI]:
    from aeon.compilation.compile import CompilationState

    state = driver.session.state(CompilationState)
    return {Path(unit.source_path).as_uri() for unit in state.modules.values()} | {
        Path(path).as_uri() for path in driver.session.source_paths
    }


def dependencies_changed(uri: URI, revision: int, dependencies: set[URI] | None = None) -> bool:
    """Check changes to this source and its actual imports, including imports
    first discovered by an analysis that was already running when they changed."""
    relevant = {uri} | _dependencies.get(uri, set()) | (dependencies or set())
    return any(_changed_at.get(dependency, 0) > revision for dependency in relevant)


def _refresh_analysis(driver: AeonDriver, uri: URI) -> None:
    """After a parse, rebuild and cache the position→type index for ``uri`` if
    core generation succeeded. On failure the previous caches are left intact."""
    _dependencies[uri] = driver_dependencies(driver)
    core = getattr(driver, "core", None)
    typing_ctx = getattr(driver, "typing_ctx", None)
    if core is None or typing_ctx is None:
        return
    try:
        from aeon.lsp.typeindex import build_type_index

        _type_index_cache[uri] = build_type_index(typing_ctx, core)
        _typing_ctx_cache[uri] = typing_ctx
        _core_cache[uri] = core
        from aeon.verification.constructor_registry import ConstructorRegistry

        _constructor_registry_cache[uri] = deepcopy(driver.session.state(ConstructorRegistry))
        metadata = getattr(driver, "metadata", None)
        if metadata is not None:
            _metadata_cache[uri] = metadata
        evaluation_ctx = getattr(driver, "evaluation_ctx", None)
        if evaluation_ctx is not None:
            _evaluation_ctx_cache[uri] = evaluation_ctx
        constructor_names = getattr(driver, "constructor_names", None)
        if constructor_names is not None:
            _constructor_names_cache[uri] = constructor_names
    except Exception:
        logger.exception("Failed to build type index for %s", uri)


def find_holes_in_source(source: str) -> List[HolePosition]:
    """Find all ?identifier holes in source text and return their LSP ranges (0-indexed)."""
    holes = []
    for line_idx, line in enumerate(source.splitlines()):
        for match in _HOLE_PATTERN.finditer(line):
            hole_range = Range(
                start=Position(line=line_idx, character=match.start()),
                end=Position(line=line_idx, character=match.end()),
            )
            holes.append(HolePosition(name=match.group(1), range=hole_range))
    return holes


_parse_result_cache: Dict[URI, ParseResult] = {}


def clear_cache(uri: URI) -> set[URI]:
    """Clear all caches for uri.
    This is to be called when the document is modified.
    """
    global _revision
    _revision += 1
    _changed_at[uri] = _revision
    affected = {uri} | {document for document, dependencies in _dependencies.items() if uri in dependencies}
    for document in affected:
        _parse_result_cache.pop(document, None)
        _parse_sources.pop(document, None)
        _errors_cache.pop(document, None)
        _proof_cache.pop(document, None)
    return affected


_isurl = re.compile("([a-zA-Z0-9+.-]+)://").match


def source_overrides(aeon_lsp: AeonLanguageServer) -> dict[str, str]:
    """Capture imported editor buffers with the same lifetime as the main file."""
    return {
        str(Path(urllib.parse.unquote(urllib.parse.urlparse(uri).path)).resolve()): document.source
        for uri, document in getattr(aeon_lsp.workspace, "text_documents", {}).items()
        if urllib.parse.urlparse(uri).scheme == "file"
    }


async def parse(
    aeon_lsp: AeonLanguageServer,
    uri: URI,
    allow_errors: bool = True,
) -> ParseResult:
    parsed_uri = urllib.parse.urlparse(uri)
    if parsed_uri.scheme in HTTP_SCHEMES:
        try:
            response = await asyncio.to_thread(requests_session.get, uri, timeout=10)
            response.raise_for_status()
            fp = io.StringIO(response.text)
        except requests.RequestException:
            fp = io.StringIO("")
    else:
        try:
            document = aeon_lsp.workspace.get_text_document(uri)
            fp = io.StringIO(document.source)
        except (IOError, KeyError, AttributeError) as exc:
            if not allow_errors:
                raise
            logger.warning("Could not read document %s: %s", uri, exc)
            return ParseResult(
                diagnostics=[
                    Diagnostic(
                        message=f"Could not read document: {exc}",
                        range=Range(
                            start=Position(line=0, character=0),
                            end=Position(line=0, character=0),
                        ),
                        source="aeon",
                        severity=DiagnosticSeverity.Error,
                    )
                ]
            )

    source = fp.read()
    if uri in _parse_result_cache and _parse_sources.get(uri) == source:
        return _parse_result_cache[uri]
    from aeon.lsp.analysis import analyze

    revision = _revision
    pending = _pending.get(uri)
    if pending is not None and pending[0] == source and not dependencies_changed(uri, pending[1]):
        revision = pending[1]
        task = pending[2]
    else:
        from dataclasses import replace

        config = replace(aeon_lsp.aeon_driver.cfg, source_overrides=source_overrides(aeon_lsp))
        task = asyncio.create_task(analyze(source, config, uri))
        _pending[uri] = (source, revision, task)
        if pending is not None:
            pending[2].cancel()
    try:
        parse_result, snapshot, dependencies = await asyncio.shield(task)
    except asyncio.CancelledError:
        replacement = _pending.get(uri)
        if task.cancelled() and replacement is not None and replacement[2] is not task:
            # Another revision superseded this analysis. Existing hover and
            # diagnostic callers join its replacement instead of seeing an error.
            return await parse(aeon_lsp, uri, allow_errors)
        raise
    finally:
        if _pending.get(uri, (None, None, None))[2] is task and task.done():
            _pending.pop(uri, None)
    # Changes may arrive while the compiler runs. Never publish stale proofs or
    # locations, including when a dependency changes during the first analysis.
    current_source = source if parsed_uri.scheme in HTTP_SCHEMES else aeon_lsp.workspace.get_text_document(uri).source
    if dependencies_changed(uri, revision, dependencies) or current_source != source:
        return await parse(aeon_lsp, uri, allow_errors)
    for key, cache in analysis_caches().items():
        if snapshot.get(key) is not None:
            cache[uri] = snapshot[key]
    _dependencies[uri] = dependencies
    _parse_result_cache[uri] = parse_result
    _parse_sources[uri] = source
    return parse_result


def _unexpected_token_diagnostic(e: UnexpectedToken) -> Diagnostic:
    token_length = 1
    try:
        token_length = len(str(e.token.value))
    except Exception:
        pass

    token_type = e.token.type if e.token.type else "unknown"
    token_value = e.token.value if e.token.value else str(e.token)

    error_message = (
        f"Unexpected {token_type} '{token_value}' at line {e.line}, column {e.column}.\n"
        f"Expected: {', '.join(e.expected)}"
    )

    error_range = Range(
        start=Position(line=e.line - 1, character=e.column - 1),
        end=Position(line=e.line - 1, character=e.column - 1 + token_length),
    )

    return Diagnostic(
        message=error_message,
        range=error_range,
        source="aeon",
        severity=DiagnosticSeverity.Error,
    )


def _unexpected_input_diagnostic(e: UnexpectedInput) -> Diagnostic:
    if isinstance(e, UnexpectedCharacters):
        char = e.char or ""
        token_length = max(len(char), 1)
        char_display = repr(char)[1:-1] if char else "character"
        allowed = sorted(e.allowed) if e.allowed else []
        error_message = (
            f"Unexpected character '{char_display}' at line {e.line}, column {e.column}.\n"
            f"Expected: {', '.join(allowed)}"
        )
        error_range = Range(
            start=Position(line=e.line - 1, character=e.column - 1),
            end=Position(line=e.line - 1, character=e.column - 1 + token_length),
        )
    else:
        error_message = str(e)
        line = getattr(e, "line", 1) or 1
        column = getattr(e, "column", 1) or 1
        error_range = Range(
            start=Position(line=line - 1, character=column - 1),
            end=Position(line=line - 1, character=column),
        )

    return Diagnostic(
        message=error_message,
        range=error_range,
        source="aeon",
        severity=DiagnosticSeverity.Error,
    )


async def _parse(
    fp: TextIO,
    driver: AeonDriver,
    uri: URI,
) -> ParseResult:
    diagnostics = []
    # Reset structured errors for this parse; only a parse that returns semantic
    # errors below repopulates them (a syntax error leaves this empty and the
    # error is surfaced as a diagnostic instead).
    _errors_cache[uri] = []
    _proof_cache[uri] = []

    try:
        content = fp.read()
        from aeon.verification.trace import collect_verification
        from aeon.lsp.verification import proof_obligations, runtime_warnings

        with collect_verification() as verification:
            try:
                errors = list(driver.parse(filename=uri, aeon_code=content))
            finally:
                _proof_cache[uri] = proof_obligations(verification, uri)

        # Keep the structured errors of this parse so the info view can render
        # their counterexamples and the failing VC's simplification chain.
        _errors_cache[uri] = errors

        # Refresh the type-aware analysis caches (kept even when `errors` is
        # non-empty, as long as the program reached core generation).
        _refresh_analysis(driver, uri)

        for error in errors:
            from aeon.errors import LiquidTypeCheckingFailedRelation

            data = None
            if isinstance(error, LiquidTypeCheckingFailedRelation):
                from aeon.verification.vcs import alpha_key

                matching = [p for p in verification if alpha_key(p.constraint) == alpha_key(error.vc)]
                if not matching:
                    from aeon.verification.trace import goal_location

                    matching = [
                        p
                        for p in verification
                        if p.status != "valid" and goal_location(p.constraint) == error.position()
                    ]
                status = matching[-1].status if matching else "unknown"
                data = {
                    "kind": "refinement",
                    "status": status,
                    "obligation": error.assumptions(),
                    "counterexample": error.counterexample() if status == "invalid" else None,
                    "reason": matching[-1].reason if matching else None,
                }
            diagnostics.append(
                Diagnostic(
                    message=str(error),
                    range=_loc_to_range(error.position()),
                    source="aeon",
                    severity=DiagnosticSeverity.Error,
                    code="refinement" if data else None,
                    data=data,
                )
            )

        diagnostics.extend(runtime_warnings(getattr(driver, "core", None), driver.cfg.contracts, uri))

        # Non-fatal decidability warnings (issue #438): refinements that leave
        # the decidable fragment z3 can reliably decide. Surface them as
        # Warning-severity diagnostics so they appear in the editor. Under strict
        # mode they are already returned as errors above, so skip them here to
        # avoid a duplicate squiggle on the same span.
        if not getattr(driver.cfg, "strict_decidable", False):
            for warning in getattr(driver, "decidability_warnings", []):
                diagnostics.append(
                    Diagnostic(
                        message=f"{warning.construct}: {warning.message}",
                        range=_loc_to_range(warning.location),
                        source="aeon",
                        severity=DiagnosticSeverity.Warning,
                    )
                )

        for warning in getattr(driver, "false_parameter_warnings", []):
            diagnostics.append(
                Diagnostic(
                    message=f"{warning.construct}: {warning.message}",
                    range=_loc_to_range(warning.location),
                    source="aeon",
                    severity=DiagnosticSeverity.Warning,
                )
            )

        if not errors:
            holes = find_holes_in_source(content)
            return ParseResult(diagnostics, holes)

    except UnexpectedToken as e:
        diagnostics.append(_unexpected_token_diagnostic(e))
    except UnexpectedInput as e:
        diagnostics.append(_unexpected_input_diagnostic(e))
    except Z3Exception as e:
        logger.warning("Z3 verification failed while parsing %s: %s", uri, e)
        diagnostics.append(
            Diagnostic(
                message=z3_diagnostic_message(e),
                range=Range(
                    start=Position(line=0, character=0),
                    end=Position(line=0, character=0),
                ),
                source="aeon",
                severity=DiagnosticSeverity.Warning,
            )
        )
        if _core_cache.get(uri) is not None:
            return ParseResult(diagnostics, find_holes_in_source(content))
    except Exception as e:
        logger.exception("Unhandled exception while parsing")
        diagnostics.append(
            Diagnostic(
                message=f"Unknown exception '{e}' occurred while parsing",
                range=Range(
                    start=Position(line=0, character=0),
                    end=Position(line=0, character=0),
                ),
                source="aeon",
                severity=DiagnosticSeverity.Error,
            )
        )
    return ParseResult(diagnostics, [])


async def _open(
    aeon_lsp: AeonLanguageServer,
    base: str,
    uri: URI,
    allow_errors: bool,
) -> ParseResult:
    logger.debug("Opening URI for parsing: base=%r, uri=%r", base, uri)
    if not _isurl(uri):
        assert base
        uri = urllib.parse.urljoin(base, uri)
    parse_result = await parse(aeon_lsp, uri, allow_errors=allow_errors)
    return parse_result
