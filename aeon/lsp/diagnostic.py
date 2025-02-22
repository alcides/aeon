import logging
from typing import AsyncIterable

from lsprotocol.types import (Diagnostic, DiagnosticRelatedInformation,
                             DiagnosticSeverity, Position, Range)
from pygls.server import LanguageServer

from ..core.types import top
from ..typechecking.typeinfer import check_type_errors

logger = logging.getLogger(__name__)

from . import buildout


async def getDiagnostics(
    ls: LanguageServer,
    uri: str,
) -> AsyncIterable[Diagnostic]:
  ast = await buildout.parse(ls, uri)
  for diag in ast.diagnostics:
      yield diag
