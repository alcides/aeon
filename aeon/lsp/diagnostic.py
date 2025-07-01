import logging
from typing import AsyncIterable

from lsprotocol.types import Diagnostic

from . import buildout
from .server import AeonLanguageServer

logger = logging.getLogger(__name__)


async def getDiagnostics(aeon_lsp: AeonLanguageServer, uri: str) -> AsyncIterable[Diagnostic]:
    ast = await buildout.parse(aeon_lsp, uri)
    for diag in ast.diagnostics:
        yield diag
