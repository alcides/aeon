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
from dataclasses import dataclass
from typing import Dict, List, TextIO

import requests
from lark.exceptions import UnexpectedToken
from lsprotocol.types import Diagnostic, DiagnosticSeverity
from lsprotocol.types import Position, Range

from aeon.facade.driver import AeonDriver
from aeon.lsp.server import AeonLanguageServer

requests_session = requests.Session()

logger = logging.getLogger(__name__)

URI = str
HTTP_SCHEMES = {"http", "https"}


@dataclass(frozen=True)
class ParseResult:
    diagnostics: List[Diagnostic]
    # Not needed for now but could be added on the future
    # core_ast: Any = None
    # typing_ctx: Any = None


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

    parse_result = await _parse(fp, aeon_lsp.aeon_driver)
    _parse_result_cache[uri] = parse_result
    return parse_result


async def _parse(
    fp: TextIO,
    driver: AeonDriver,
) -> ParseResult:
    diagnostics = []

    try:
        content = fp.read()
        errors = driver.parse(aeon_code=content)

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
    return ParseResult(diagnostics)


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
