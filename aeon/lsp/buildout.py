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

import copy
import io
import logging
import re
import urllib.parse
from typing import Dict, List, TextIO

import requests
from lark.exceptions import UnexpectedToken
from lsprotocol.types import Diagnostic, DiagnosticSeverity
from lsprotocol.types import Position, Range

from aeon.facade.driver import AeonDriver
from aeon.lsp.server import AeonLanguageServer

logger = logging.getLogger(__name__)
requests_session = requests.Session()

# type definitions #
URI = str  # type alias


class AST:
    def __init__(self, core_ast_anf, typing_ctx, diagnostics):
        self.core_ast_anf = core_ast_anf
        self.typing_ctx = typing_ctx
        self.diagnostics = diagnostics


# cache #
# a cache of un-resolved buildouts by uri
_parse_cache: Dict[URI, AST] = {}


def clearCache(uri: URI) -> None:
    """Clear all caches for uri.
    This is to be called when the document is modified.
    """
    logger.debug("Clearing cache for %s", uri)
    _parse_cache.pop(uri, None)
    logger.debug("DONE!")


# buildout copied & modified functions #

_isurl = re.compile("([a-zA-Z0-9+.-]+)://").match


async def parse(
    aeon_lsp: AeonLanguageServer,
    uri: URI,
    allow_errors: bool = True,
) -> AST:
    """
    Parse a sectioned setup file and return a non-resolved buildout.

    This is a wrapper over _parse which uses language server's workspace to access documents.
    Returned value changed to a BuildoutProfile instance.

    """
    if uri in _parse_cache:
        return copy.deepcopy(_parse_cache[uri])

    parsed_uri = urllib.parse.urlparse(uri)
    if parsed_uri.scheme in (
        "http",
        "https",
    ):
        try:
            fp = io.StringIO(requests_session.get(uri).text)
        except requests.exceptions.ConnectionError:
            fp = io.StringIO("")
    else:
        document = aeon_lsp.workspace.get_text_document(uri)
        try:
            fp = io.StringIO(document.source)
        except IOError:
            if not allow_errors:
                raise
            fp = io.StringIO("")
    parsed = await _parse(fp, aeon_lsp.aeon_driver)
    _parse_cache[uri] = copy.deepcopy(parsed)
    return parsed


async def _parse(
    fp: TextIO,
    driver: AeonDriver,
) -> AST:
    """
    Parse the code
    """
    diagnostics = []
    core_ast_anf = None
    typing_ctx = None

    try:
        content = fp.read()
        errors = driver.parse(aeon_code=content)

        for error in errors:
            error_message = str(error)
            error_position = error.position()

            error_start_line, error_start_column = error_position.start()
            error_end_line, error_end_column = error_position.end()

            error_range = Range(
                start=Position(line=error_start_line, character=error_start_column),
                end=Position(line=error_end_line, character=error_end_column),
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
        try:
            token_length = len(str(e.token.value))
        except Exception:
            token_length = 1

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
        diagnostics.append(
            Diagnostic(
                message=f"Unknown exception {str(e)} occurred while parsing",
                range=Range(start=Position(line=0, character=0), end=Position(line=0, character=0)),
                source="aeon",
                severity=DiagnosticSeverity.Error,
            )
        )
    return AST(core_ast_anf, typing_ctx, diagnostics)


async def _open(
    aeon_lsp: AeonLanguageServer,
    base: str,
    uri: URI,
    seen: List[str],
    allow_errors: bool,
) -> AST:
    """Open a configuration file and return the result as a dictionary,

    Recursively open other files based on buildout options found.

    This is equivalent of zc.buildout.buildout._open
    """
    logger.debug("_open %r %r", base, uri)

    if not _isurl(uri):
        assert base
        uri = urllib.parse.urljoin(base, uri)
    result = await parse(aeon_lsp, uri, allow_errors=allow_errors)
    return copy.deepcopy(result)
