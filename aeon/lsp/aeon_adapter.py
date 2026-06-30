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
import logging
import re
import urllib.parse
from dataclasses import dataclass, field
from typing import Dict, List, TextIO

import requests
from lark.exceptions import UnexpectedToken
from lsprotocol.types import Diagnostic, DiagnosticSeverity
from lsprotocol.types import Position, Range

from aeon.facade.driver import AeonDriver
from aeon.lsp.server import AeonLanguageServer, _loc_to_range

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


def get_type_index(uri: URI):
    """The last successfully-built ``TypeIndex`` for ``uri`` (or ``None``)."""
    return _type_index_cache.get(uri)


def get_typing_ctx(uri: URI):
    """The last successful top-level typing context for ``uri`` (or ``None``)."""
    return _typing_ctx_cache.get(uri)


def get_core(uri: URI):
    """The last successfully-generated core program for ``uri`` (or ``None``)."""
    return _core_cache.get(uri)


def _refresh_analysis(driver: AeonDriver, uri: URI) -> None:
    """After a parse, rebuild and cache the position→type index for ``uri`` if
    core generation succeeded. On failure the previous caches are left intact."""
    core = getattr(driver, "core", None)
    typing_ctx = getattr(driver, "typing_ctx", None)
    if core is None or typing_ctx is None:
        return
    try:
        from aeon.lsp.typeindex import build_type_index

        _type_index_cache[uri] = build_type_index(typing_ctx, core)
        _typing_ctx_cache[uri] = typing_ctx
        _core_cache[uri] = core
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


def clear_cache(uri: URI) -> None:
    """Clear all caches for uri.
    This is to be called when the document is modified.
    """
    logger.debug("Clearing cache for %s", uri)
    _parse_result_cache.pop(uri, None)
    logger.debug("DONE!")


_isurl = re.compile("([a-zA-Z0-9+.-]+)://").match


async def parse(
    aeon_lsp: AeonLanguageServer,
    uri: URI,
    allow_errors: bool = True,
) -> ParseResult:
    if uri in _parse_result_cache:
        return _parse_result_cache[uri]

    parsed_uri = urllib.parse.urlparse(uri)
    if parsed_uri.scheme in HTTP_SCHEMES:
        try:
            response = requests_session.get(uri)
            response.raise_for_status()
            fp = io.StringIO(response.text)
        except requests.RequestException:
            fp = io.StringIO("")
    else:
        document = aeon_lsp.workspace.get_text_document(uri)
        try:
            fp = io.StringIO(document.source)
        except IOError:
            if not allow_errors:
                raise
            fp = io.StringIO("")

    parse_result = await _parse(fp, aeon_lsp.aeon_driver, uri)
    _parse_result_cache[uri] = parse_result
    return parse_result


async def _parse(
    fp: TextIO,
    driver: AeonDriver,
    uri: URI,
) -> ParseResult:
    diagnostics = []

    try:
        content = fp.read()
        errors = driver.parse(filename=uri, aeon_code=content)

        # Refresh the type-aware analysis caches (kept even when `errors` is
        # non-empty, as long as the program reached core generation).
        _refresh_analysis(driver, uri)

        for error in errors:
            error_message = str(error)
            error_position = error.position()

            error_start_line, error_start_character = error_position.get_start()
            error_end_line, error_end_character = error_position.get_end()

            error_range = Range(
                start=Position(line=error_start_line, character=error_start_character),
                end=Position(line=error_end_line, character=error_end_character),
            )

            diagnostics.append(
                Diagnostic(
                    message=error_message,
                    range=error_range,
                    source="aeon",
                    severity=DiagnosticSeverity.Error,
                )
            )

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

        if not errors:
            holes = find_holes_in_source(content)
            return ParseResult(diagnostics, holes)

    except UnexpectedToken as e:
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

        diagnostics.append(
            Diagnostic(
                message=error_message,
                range=error_range,
                source="aeon",
                severity=DiagnosticSeverity.Error,
            )
        )
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
