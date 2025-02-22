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

import collections
import copy
import io
import logging
import os
import re
import textwrap
import enum
import urllib.parse
import pathlib
from pydoc_data.topics import topics

from typing import TYPE_CHECKING, Dict, List, Iterator, Tuple, Optional, Set, TextIO, Union, Match, cast, AsyncIterator, \
    Any, Coroutine
from lsprotocol.types import Diagnostic, DiagnosticSeverity

from pygls.server import LanguageServer
from pygls.workspace import Document
from lsprotocol.types import Position, Range, Location

import requests

from aeon.core.types import top
from aeon.frontend.anf_converter import ensure_anf
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.sugar.program import Program
from aeon.typechecking.typeinfer import check_type_errors

logger = logging.getLogger(__name__)
requests_session = requests.Session()

### type definitions ###
URI = str  # type alias

class AST:
  def __init__(self, core_ast_anf, typing_ctx, diagnostics):
    self.core_ast_anf = core_ast_anf
    self.typing_ctx = typing_ctx
    self.diagnostics = diagnostics

### cache ###

# a cache of un-resolved buildouts by uri
_parse_cache: Dict[URI, AST] = {}


def clearCache(uri: URI) -> None:
  """Clear all caches for uri.

  This is to be called when the document is modified.
  """
  logger.debug("Clearing cache for %s", uri)
  _parse_cache.pop(uri)
  logger.debug("DONE!")


### buildout copied & modified functions ###

_isurl = re.compile('([a-zA-Z0-9+.-]+)://').match


async def parse(
    ls: LanguageServer,
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
      'http',
      'https',
  ):
    try:
      fp = io.StringIO(requests_session.get(uri).text)
    except requests.exceptions.ConnectionError:
      fp = io.StringIO('')
  else:
    document = ls.workspace.get_document(uri)
    try:
      fp = io.StringIO(document.source)
    except IOError:
      if not allow_errors:
        raise
      fp = io.StringIO('')
  parsed = await _parse(
      fp,
      uri,
      allow_errors,
  )
  _parse_cache[uri] = copy.deepcopy(parsed)
  return parsed


async def _parse(
    fp: TextIO,
    uri: URI,
    allow_errors: bool,
) -> AST:
  """
  Parse the code

  """
  content = fp.read()
  fp.seek(0)
  program = parse_program(content)
  (
      core_ast,
      typing_ctx,
      _,
      _
  ) = desugar(program)
  core_ast_anf = ensure_anf(core_ast)
  errors = check_type_errors(typing_ctx, core_ast_anf, top)
  diagnostics = []
  for error in errors:
      range = Range(start=Position(line=0, character=0), #needs to be fixed
                  end=Position(line=0, character=0))
      curr_diagnostic = Diagnostic(
        message=error,
        range=range,
        source="aeon",
        severity=DiagnosticSeverity.Error,
      )
      diagnostics.append(curr_diagnostic)
  return AST(core_ast_anf, typing_ctx,diagnostics)


async def _open(
    ls: LanguageServer,
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
  result = await parse(ls, uri, allow_errors=allow_errors)
  return copy.deepcopy(result)
