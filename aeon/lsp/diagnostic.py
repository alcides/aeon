import logging
from typing import AsyncIterable

from lsprotocol.types import Diagnostic
from pygls.server import LanguageServer

from . import buildout

logger = logging.getLogger(__name__)


async def getDiagnostics(
    ls: LanguageServer,
    uri: str,
) -> AsyncIterable[Diagnostic]:
    ast = await buildout.parse(ls, uri)
    for diag in ast.diagnostics:
        yield diag
