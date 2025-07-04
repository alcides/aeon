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

from ..facade.driver import AeonDriver


class AeonLanguageServer(LanguageServer):
    def __init__(self, aeon_driver: AeonDriver):
        super().__init__("aeon.lsp.server", "0.1.0")
        self.aeon_driver = aeon_driver
        self.debounce_delay = 0.3
        self._setup_handlers()

    def start(self, tcp_server):
        if not tcp_server:
            self.start_io()

        host, port = tcp_server.split(":") if ":" in tcp_server else ("localhost", tcp_server)

        print(f"Listening on {host}:{port}")
        self.start_tcp(host, int(port))

    async def parseAndSendDiagnostics(self, uri) -> None:
        from . import diagnostic

        await asyncio.sleep(self.debounce_delay)
        diagnostics = []
        async for diag in diagnostic.getDiagnostics(self.server, uri):
            diagnostics.append(diag)
        self.server.publish_diagnostics(uri, diagnostics)

    def _setup_handlers(self):
        @self.feature(TEXT_DOCUMENT_DID_OPEN)
        async def did_open(
            ls: AeonLanguageServer,
            params: DidOpenTextDocumentParams,
        ) -> None:
            await self.parseAndSendDiagnostics(params.text_document.uri)

        @self.feature(TEXT_DOCUMENT_DID_CHANGE)
        async def did_change(
            ls: AeonLanguageServer,
            params: DidChangeTextDocumentParams,
        ) -> None:
            from . import buildout

            buildout.clearCache(params.text_document.uri)
            await self.parseAndSendDiagnostics(params.text_document.uri)

        @self.feature(WORKSPACE_DID_CHANGE_WATCHED_FILES)
        async def did_change_watched_file(
            ls: AeonLanguageServer,
            params: DidChangeWatchedFilesParams,
        ) -> None:
            from . import buildout

            for change in params.changes:
                buildout.clearCache(change.uri)

        @self.feature(TEXT_DOCUMENT_COMPLETION, CompletionOptions(trigger_characters=["= "]))
        async def lsp_completion(
            ls: AeonLanguageServer,
            params: CompletionParams,
        ) -> Optional[List[CompletionItem]]:
            await asyncio.sleep(self.debounce_delay)
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
