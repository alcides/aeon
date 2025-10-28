import asyncio
from typing import List, Optional, AsyncIterable

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
    Diagnostic,
    PublishDiagnosticsParams,
)
from pygls.lsp.server import LanguageServer

from aeon.facade.driver import AeonDriver


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

    async def _parse_and_send_diagnostics(self, uri) -> None:
        await asyncio.sleep(self.debounce_delay)
        diagnostics = []
        async for diag in self._get_diagnostics(uri):
            diagnostics.append(diag)
        self.text_document_publish_diagnostics(PublishDiagnosticsParams(uri=uri, diagnostics=diagnostics))

    async def _get_diagnostics(self, uri: str) -> AsyncIterable[Diagnostic]:
        from . import aeon_adapter

        ast = await aeon_adapter.parse(self, uri)
        for diag in ast.diagnostics:
            yield diag

    def _setup_handlers(self):
        @self.feature(TEXT_DOCUMENT_DID_OPEN)
        async def did_open(
            ls: AeonLanguageServer,
            params: DidOpenTextDocumentParams,
        ) -> None:
            await ls._parse_and_send_diagnostics(params.text_document.uri)

        @self.feature(TEXT_DOCUMENT_DID_CHANGE)
        async def did_change(
            ls: AeonLanguageServer,
            params: DidChangeTextDocumentParams,
        ) -> None:
            from . import aeon_adapter

            aeon_adapter.clear_cache(params.text_document.uri)
            await ls._parse_and_send_diagnostics(params.text_document.uri)

        @self.feature(WORKSPACE_DID_CHANGE_WATCHED_FILES)
        async def did_change_watched_file(
            ls: AeonLanguageServer,
            params: DidChangeWatchedFilesParams,
        ) -> None:
            from . import aeon_adapter

            for change in params.changes:
                aeon_adapter.clear_cache(change.uri)

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
