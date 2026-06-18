import asyncio
from typing import List, Optional, AsyncIterable

from lsprotocol.types import (
    TEXT_DOCUMENT_CODE_ACTION,
    TEXT_DOCUMENT_COMPLETION,
    TEXT_DOCUMENT_DEFINITION,
    TEXT_DOCUMENT_DID_OPEN,
    TEXT_DOCUMENT_DID_CHANGE,
    TEXT_DOCUMENT_DOCUMENT_SYMBOL,
    TEXT_DOCUMENT_HOVER,
    TEXT_DOCUMENT_INLAY_HINT,
    WORKSPACE_DID_CHANGE_WATCHED_FILES,
    ApplyWorkspaceEditParams,
    CodeAction,
    CodeActionKind,
    CodeActionOptions,
    CodeActionParams,
    Command,
    CompletionItem,
    CompletionItemKind,
    CompletionItemTag,
    CompletionOptions,
    CompletionParams,
    DefinitionParams,
    DidChangeTextDocumentParams,
    DidChangeWatchedFilesParams,
    DidOpenTextDocumentParams,
    Diagnostic,
    DocumentSymbol,
    DocumentSymbolParams,
    Hover,
    HoverParams,
    InlayHint,
    InlayHintKind,
    InlayHintParams,
    Location,
    MarkupContent,
    MarkupKind,
    MessageType,
    Position,
    PublishDiagnosticsParams,
    ShowMessageParams,
    Range,
    SymbolKind,
    TextEdit,
    WorkspaceEdit,
)
from pygls.lsp.server import LanguageServer

from aeon.facade.driver import AeonDriver

SYNTHESIZERS = [
    "tdsyn_enumerative",
    "tdsyn",
    "tactics",
    "gp",
    "enumerative",
    "random_search",
    "synquid",
    "hc",
    "1p1",
    "smt",
    "sygus",
    "decision_tree",
    "llm",
    "fta",
    "afta",
    "cata",
    "lta",
    "symetric",
]
SYNTHESIZE_COMMAND = "aeon.synthesize"

# Custom (non-standard) request backing the editor's Lean-style info view
# panel. Params: {"textDocument": {"uri": ...}, "position": {"line": ..., "character": ...}}
# (0-indexed, LSP convention). Response: the JSON form of
# :class:`aeon.lsp.infoview.InfoViewData`.
INFOVIEW_REQUEST = "aeon/infoView"


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
            from . import aeon_adapter
            from aeon.lsp.completion import format_type

            document = ls.workspace.get_text_document(params.text_document.uri)
            source = document.source
            line, character = params.position.line, params.position.character
            word = _get_word_at_position(source, line, character)

            # Position-accurate hover: the inferred (refined) type of the
            # expression under the cursor, from the type index.
            index = aeon_adapter.get_type_index(params.text_document.uri)
            if index is not None:
                result = index.type_at(line, character)
                if result is not None:
                    ty, loc = result
                    lhs = f"{word} : " if word else ""
                    return Hover(
                        contents=MarkupContent(
                            kind=MarkupKind.Markdown,
                            value=f"```aeon\n{lhs}{format_type(ty)}\n```",
                        ),
                        range=_loc_to_range(loc),
                    )

            # Fallback: top-level name match (e.g. hovering a definition's name,
            # which is a binder and has no synthesized-expression observation).
            if not word:
                return None
            typing_ctx = aeon_adapter.get_typing_ctx(params.text_document.uri) or getattr(
                ls.aeon_driver, "typing_ctx", None
            )
            if typing_ctx is None:
                return None
            for name, type_ in typing_ctx.vars():
                if name.pretty() == word:
                    return Hover(
                        contents=MarkupContent(
                            kind=MarkupKind.Markdown,
                            value=f"```aeon\n{word} : {format_type(type_)}\n```",
                        )
                    )
            return None

        @self.feature(TEXT_DOCUMENT_COMPLETION, CompletionOptions(trigger_characters=["."]))
        async def lsp_completion(
            ls: AeonLanguageServer,
            params: CompletionParams,
        ) -> Optional[List[CompletionItem]]:
            from . import aeon_adapter
            from aeon.lsp.completion import compute_completions

            document = ls.workspace.get_text_document(params.text_document.uri)
            source = document.source
            index = aeon_adapter.get_type_index(params.text_document.uri)
            typing_ctx = aeon_adapter.get_typing_ctx(params.text_document.uri) or getattr(
                ls.aeon_driver, "typing_ctx", None
            )
            try:
                completions = compute_completions(
                    source, params.position.line, params.position.character, typing_ctx, index
                )
            except Exception:
                return []
            return [_to_completion_item(c) for c in completions]

        @self.feature(TEXT_DOCUMENT_INLAY_HINT)
        async def inlay_hint(
            ls: AeonLanguageServer,
            params: InlayHintParams,
        ) -> Optional[List[InlayHint]]:
            from . import aeon_adapter
            from aeon.lsp.navigation import inlay_hints

            uri = params.text_document.uri
            core = aeon_adapter.get_core(uri)
            index = aeon_adapter.get_type_index(uri)
            if core is None or index is None:
                return []
            document = ls.workspace.get_text_document(uri)
            hints = []
            for h in inlay_hints(core, document.source, index):
                # 1-indexed core positions -> 0-indexed LSP.
                hints.append(
                    InlayHint(
                        position=Position(line=h.line - 1, character=h.character - 1),
                        label=h.label,
                        kind=InlayHintKind.Type,
                        padding_left=True,
                    )
                )
            return hints

        @self.feature(TEXT_DOCUMENT_DEFINITION)
        async def definition(
            ls: AeonLanguageServer,
            params: DefinitionParams,
        ) -> Optional[Location]:
            from . import aeon_adapter
            from aeon.lsp.navigation import build_def_index

            uri = params.text_document.uri
            core = aeon_adapter.get_core(uri)
            if core is None:
                return None
            document = ls.workspace.get_text_document(uri)
            def_index = build_def_index(core, document.source)
            span = def_index.definition_at(params.position.line, params.position.character)
            if span is None:
                return None
            return Location(uri=uri, range=_span_to_range(span))

        @self.feature(TEXT_DOCUMENT_DOCUMENT_SYMBOL)
        async def document_symbol(
            ls: AeonLanguageServer,
            params: DocumentSymbolParams,
        ) -> Optional[List[DocumentSymbol]]:
            from . import aeon_adapter
            from aeon.lsp.navigation import document_symbols

            uri = params.text_document.uri
            core = aeon_adapter.get_core(uri)
            if core is None:
                return []
            document = ls.workspace.get_text_document(uri)
            out = []
            for s in document_symbols(core, document.source):
                out.append(
                    DocumentSymbol(
                        name=s.name,
                        detail=s.detail,
                        kind=SymbolKind.Function if s.is_function else SymbolKind.Variable,
                        range=_span_to_range(s.full_range),
                        selection_range=_span_to_range(s.selection_range),
                    )
                )
            return out

        @self.feature(INFOVIEW_REQUEST)
        async def info_view(
            ls: AeonLanguageServer,
            params,
        ) -> dict:
            from . import aeon_adapter
            from aeon.lsp.infoview import InfoViewData, compute_info_view

            # Custom method: params arrive as a generic pygls ``Object`` with
            # the wire-format (camelCase) attribute names.
            uri = params.textDocument.uri
            line = params.position.line
            character = params.position.character

            # Make sure the document has been analysed at least once (cached).
            await aeon_adapter.parse(ls, uri)

            document = ls.workspace.get_text_document(uri)
            index = aeon_adapter.get_type_index(uri)
            typing_ctx = aeon_adapter.get_typing_ctx(uri) or getattr(ls.aeon_driver, "typing_ctx", None)
            core = aeon_adapter.get_core(uri)
            try:
                data = compute_info_view(document.source, line, character, typing_ctx, index, core)
            except Exception:
                return InfoViewData().to_dict()
            return data.to_dict()

        @self.feature(
            TEXT_DOCUMENT_CODE_ACTION,
            CodeActionOptions(code_action_kinds=[CodeActionKind.RefactorRewrite]),
        )
        async def code_action(
            ls: AeonLanguageServer,
            params: CodeActionParams,
        ) -> Optional[List[CodeAction]]:
            from . import aeon_adapter
            from aeon.synthesis.modules.synthesizerfactory import synthesizer_label

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
                    label = synthesizer_label(synthesizer)
                    action = CodeAction(
                        title=f"Synthesize ?{hole.name} with {label}",
                        kind=CodeActionKind.RefactorRewrite,
                        command=Command(
                            title=f"Synthesize ?{hole.name} with {label}",
                            command=SYNTHESIZE_COMMAND,
                            # The internal id is what make_synthesizer expects.
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


_COMPLETION_KIND_MAP = {
    "method": CompletionItemKind.Method,
    "function": CompletionItemKind.Function,
    "variable": CompletionItemKind.Variable,
}


def _loc_to_range(loc) -> Range:
    """Convert a 1-indexed core ``FileLocation`` to a 0-indexed LSP ``Range``."""
    (sl, sc), (el, ec) = loc.get_start(), loc.get_end()
    return Range(
        start=Position(line=max(sl - 1, 0), character=max(sc - 1, 0)),
        end=Position(line=max(el - 1, 0), character=max(ec - 1, 0)),
    )


def _span_to_range(span) -> Range:
    """Convert a 1-indexed ``(sl, sc, el, ec)`` span to a 0-indexed LSP ``Range``."""
    sl, sc, el, ec = span
    return Range(
        start=Position(line=max(sl - 1, 0), character=max(sc - 1, 0)),
        end=Position(line=max(el - 1, 0), character=max(ec - 1, 0)),
    )


def _to_completion_item(c) -> CompletionItem:
    """Map a :class:`aeon.lsp.completion.Completion` to an LSP ``CompletionItem``.

    Tier-3-infeasible candidates are tagged ``Deprecated`` so editors render them
    struck-through, and their ``sortText`` already sinks them below feasible
    ones."""
    tags = [CompletionItemTag.Deprecated] if not c.feasible else None
    documentation = MarkupContent(kind=MarkupKind.Markdown, value=c.documentation) if c.documentation else None
    return CompletionItem(
        label=c.label,
        kind=_COMPLETION_KIND_MAP.get(c.kind, CompletionItemKind.Text),
        detail=c.detail,
        documentation=documentation,
        insert_text=c.insert_text,
        sort_text=c.sort_text,
        tags=tags,
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
