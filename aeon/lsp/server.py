import asyncio
from typing import List, Optional

from lsprotocol.types import (
    TEXT_DOCUMENT_COMPLETION,
    TEXT_DOCUMENT_DID_OPEN,
    TEXT_DOCUMENT_DID_CHANGE,
    WORKSPACE_DID_CHANGE_WATCHED_FILES,
    CompletionItem,
    CompletionOptions,
    CompletionParams,
    DidChangeTextDocumentParams,
    DidChangeWatchedFilesParams,
    DidOpenTextDocumentParams,
)
from pygls.server import LanguageServer

from . import buildout, diagnostic

server = LanguageServer("aeon.lsp.server", "0.1.0")
DEBOUNCE_DELAY = 0.3


def start_language_server_mode(tcp_server):
    if not tcp_server:
        server.start_io()

    host, port = (tcp_server.split(':') if ':' in tcp_server else ('localhost', tcp_server))

    print(f'Listening on {host}:{port}')
    server.start_tcp(host, int(port))


async def parseAndSendDiagnostics(
    ls: LanguageServer,
    uri: str,
) -> None:
    await asyncio.sleep(DEBOUNCE_DELAY)
    diagnostics = []
    async for diag in diagnostic.getDiagnostics(ls, uri):
        diagnostics.append(diag)
    ls.publish_diagnostics(uri, diagnostics)


@server.feature(TEXT_DOCUMENT_DID_OPEN)
async def did_open(
    ls: LanguageServer,
    params: DidOpenTextDocumentParams,
) -> None:
    await parseAndSendDiagnostics(ls, params.text_document.uri)


@server.feature(TEXT_DOCUMENT_DID_CHANGE)
async def did_change(
    ls: LanguageServer,
    params: DidChangeTextDocumentParams,
) -> None:
    buildout.clearCache(params.text_document.uri)
    await parseAndSendDiagnostics(ls, params.text_document.uri)


@server.feature(WORKSPACE_DID_CHANGE_WATCHED_FILES)
async def did_change_watched_file(
    _: LanguageServer,
    params: DidChangeWatchedFilesParams,
) -> None:
    for change in params.changes:
        buildout.clearCache(change.uri)


@server.feature(TEXT_DOCUMENT_COMPLETION, CompletionOptions(trigger_characters=["= "]))
async def lsp_completion(
    ls: LanguageServer,
    params: CompletionParams,
) -> Optional[List[CompletionItem]]:
    await asyncio.sleep(DEBOUNCE_DELAY)
    return []  # TODO
    # items: List[CompletionItem] = []
    #
    # ast = await buildout.parse(ls, params.text_document.uri, True)
    # for line in ast.lines:
    #   pos = params.position
    #   (var_name, var_type, value) = line
    #   ci = CompletionItem(
    #       label=var_name,
    #       text_edit=TextEdit(
    #           range=Range(start=Position(line=pos.line, character=pos.character),
    #                       end=Position(line=pos.line,
    #                                    character=pos.character + len(var_name))),
    #           new_text=var_name,
    #       ),
    #       kind=CompletionItemKind.Variable,
    #       documentation=MarkupContent(
    #           kind=MarkupKind.Markdown,
    #           value=f"{var_name} : {var_type} = {value}",
    #       ))
    #   items.append(ci)
    # return items
