import asyncio
from typing import List, Optional, AsyncIterable

from lsprotocol.types import (
    TEXT_DOCUMENT_CODE_ACTION,
    TEXT_DOCUMENT_COMPLETION,
    TEXT_DOCUMENT_DID_OPEN,
    TEXT_DOCUMENT_DID_CHANGE,
    TEXT_DOCUMENT_HOVER,
    WORKSPACE_DID_CHANGE_WATCHED_FILES,
    ApplyWorkspaceEditParams,
    CodeAction,
    CodeActionKind,
    CodeActionOptions,
    CodeActionParams,
    Command,
    CompletionItem,
    CompletionOptions,
    CompletionParams,
    DidChangeTextDocumentParams,
    DidChangeWatchedFilesParams,
    DidOpenTextDocumentParams,
    Diagnostic,
    Hover,
    HoverParams,
    MarkupContent,
    MarkupKind,
    MessageType,
    PublishDiagnosticsParams,
    ShowMessageParams,
    Range,
    TextEdit,
    WorkspaceEdit,
)
from pygls.lsp.server import LanguageServer

from aeon.facade.driver import AeonDriver

SYNTHESIZERS = [
    "tdsyn",
    "tdsyn_random",
    "gp",
    "enumerative",
    "random_search",
    "synquid",
    "hc",
    "1p1",
    "smt",
    "decision_tree",
    "llm",
]
SYNTHESIZE_COMMAND = "aeon.synthesize"


class AeonLanguageServer(LanguageServer):
    def __init__(self, aeon_driver: AeonDriver):
        super().__init__("aeon.lsp.server", "0.1.0")
        self.aeon_driver = aeon_driver
        self.debounce_delay = 0.3
        self._setup_handlers()

    def start(self, tcp_server):
        if not tcp_server:
            self.start_io()
            return

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

    def _ranges_overlap(self, r1: Range, r2: Range) -> bool:
        """Return True if two LSP ranges overlap (touching at a boundary counts)."""
        if r1.end.line < r2.start.line or r2.end.line < r1.start.line:
            return False
        if r1.end.line == r2.start.line and r1.end.character < r2.start.character:
            return False
        if r2.end.line == r1.start.line and r2.end.character < r1.start.character:
            return False
        return True

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

        @self.feature(TEXT_DOCUMENT_HOVER)
        async def hover(
            ls: AeonLanguageServer,
            params: HoverParams,
        ) -> Optional[Hover]:
            await asyncio.sleep(ls.debounce_delay)
            document = ls.workspace.get_text_document(params.text_document.uri)
            source = document.source
            word = _get_word_at_position(source, params.position.line, params.position.character)
            if not word:
                return None
            try:
                typing_ctx = ls.aeon_driver.typing_ctx
            except AttributeError:
                return None
            for name, type_ in typing_ctx.vars():
                if name.pretty() == word:
                    return Hover(
                        contents=MarkupContent(
                            kind=MarkupKind.Markdown,
                            value=f"```\n{word} : {type_}\n```",
                        )
                    )
            return None

        @self.feature(TEXT_DOCUMENT_COMPLETION, CompletionOptions(trigger_characters=["= "]))
        async def lsp_completion(
            ls: AeonLanguageServer,
            params: CompletionParams,
        ) -> Optional[List[CompletionItem]]:
            await asyncio.sleep(ls.debounce_delay)
            return []

        @self.feature(
            TEXT_DOCUMENT_CODE_ACTION,
            CodeActionOptions(code_action_kinds=[CodeActionKind.RefactorRewrite]),
        )
        async def code_action(
            ls: AeonLanguageServer,
            params: CodeActionParams,
        ) -> Optional[List[CodeAction]]:
            from . import aeon_adapter

            uri = params.text_document.uri
            cursor_range = params.range

            parse_result = await aeon_adapter.parse(ls, uri)
            if not parse_result.holes:
                return []

            actions = []
            for hole in parse_result.holes:
                if not ls._ranges_overlap(hole.range, cursor_range):
                    continue
                for synthesizer in SYNTHESIZERS:
                    action = CodeAction(
                        title=f"Synthesize ?{hole.name} with {synthesizer}",
                        kind=CodeActionKind.RefactorRewrite,
                        command=Command(
                            title=f"Synthesize ?{hole.name} with {synthesizer}",
                            command=SYNTHESIZE_COMMAND,
                            arguments=[uri, hole.name, synthesizer],
                        ),
                    )
                    actions.append(action)
            return actions

        @self.command(SYNTHESIZE_COMMAND)
        async def execute_synthesize(
            ls: AeonLanguageServer,
            uri: str,
            hole_name_str: str,
            synthesizer_name: str,
        ) -> None:
            loop = asyncio.get_event_loop()
            try:
                result = await loop.run_in_executor(
                    None,
                    lambda: _run_synthesis(ls.aeon_driver, ls, uri, hole_name_str, synthesizer_name),
                )
            except Exception as e:
                ls.window_show_message(ShowMessageParams(type=MessageType.Error, message=f"Synthesis error: {e}"))
                return

            if result is None:
                return

            synthesized_str, hole_range = result
            edit = TextEdit(range=hole_range, new_text=synthesized_str)
            workspace_edit = WorkspaceEdit(changes={uri: [edit]})
            ls.workspace_apply_edit(ApplyWorkspaceEditParams(edit=workspace_edit))
            ls.window_show_message(
                ShowMessageParams(type=MessageType.Info, message=f"Synthesized ?{hole_name_str} = {synthesized_str}")
            )


def _get_word_at_position(source: str, line: int, character: int) -> Optional[str]:
    """Return the identifier token under the cursor, or None if none."""
    lines = source.splitlines()
    if line >= len(lines):
        return None
    line_text = lines[line]
    col = character
    # Step over a leading '?' so hovering on ?hole returns the hole name
    if col < len(line_text) and line_text[col] == "?":
        col += 1
    if col >= len(line_text):
        return None
    start = col
    while start > 0 and (line_text[start - 1].isalnum() or line_text[start - 1] == "_"):
        start -= 1
    end = col
    while end < len(line_text) and (line_text[end].isalnum() or line_text[end] == "_"):
        end += 1
    if start == end:
        return None
    word = line_text[start:end]
    if not word or not (word[0].isalpha() or word[0] == "_"):
        return None
    return word


def _run_synthesis(driver: AeonDriver, ls: AeonLanguageServer, uri: str, hole_name_str: str, synthesizer_name: str):
    """Blocking synthesis function, meant to run in a thread executor."""
    from . import aeon_adapter
    from aeon.synthesis.entrypoint import synthesize_holes
    from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
    from aeon.synthesis.uis.api import SilentSynthesisUI
    from aeon.sugar.lifting import lift
    from aeon.utils.pprint import pretty_print_sterm

    document = ls.workspace.get_text_document(uri)
    source = document.source

    try:
        errors = list(driver.parse(filename=uri, aeon_code=source))
    except Exception as e:
        ls.window_show_message(
            ShowMessageParams(type=MessageType.Error, message=f"Cannot synthesize: parse failed ({e})")
        )
        return None
    if errors:
        ls.window_show_message(
            ShowMessageParams(type=MessageType.Error, message=f"Cannot synthesize: file has {len(errors)} error(s)")
        )
        return None

    if not driver.has_synth():
        ls.window_show_message(ShowMessageParams(type=MessageType.Info, message="No holes found in file"))
        return None

    targets = [(fn, holes) for fn, holes in driver.incomplete_functions if any(h.name == hole_name_str for h in holes)]

    if not targets:
        ls.window_show_message(
            ShowMessageParams(type=MessageType.Warning, message=f"Hole ?{hole_name_str} not found or not synthesizable")
        )
        return None

    ls.window_show_message(
        ShowMessageParams(type=MessageType.Info, message=f"Synthesizing ?{hole_name_str} with {synthesizer_name}...")
    )

    try:
        synthesizer = make_synthesizer(synthesizer_name)
    except AssertionError:
        ls.window_show_message(
            ShowMessageParams(type=MessageType.Error, message=f"Unknown synthesizer: {synthesizer_name}")
        )
        return None

    ui = SilentSynthesisUI()
    try:
        mapping = synthesize_holes(
            driver.typing_ctx,
            driver.evaluation_ctx,
            driver.core,
            targets,
            driver.metadata,
            synthesizer,
            budget=5.0,
            ui=ui,
        )
    except Exception as e:
        ls.window_show_message(ShowMessageParams(type=MessageType.Error, message=f"Synthesis failed: {e}"))
        return None

    for hole_name, term in mapping.items():
        if hole_name.name == hole_name_str and term is not None:
            sterm = lift(term)
            synthesized_str = pretty_print_sterm(sterm)

            hole_positions = aeon_adapter.find_holes_in_source(source)
            hole_range = next(
                (h.range for h in hole_positions if h.name == hole_name_str),
                None,
            )
            if hole_range is None:
                ls.window_show_message(
                    ShowMessageParams(type=MessageType.Error, message=f"Could not locate ?{hole_name_str} in source")
                )
                return None

            return synthesized_str, hole_range

    ls.window_show_message(
        ShowMessageParams(type=MessageType.Warning, message=f"No solution found for ?{hole_name_str}")
    )
    return None
