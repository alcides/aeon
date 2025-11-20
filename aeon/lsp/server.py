import asyncio
from dataclasses import dataclass
from functools import partial
from typing import AsyncIterable, Dict, List, Optional, Tuple
from urllib.parse import unquote, urlparse

from lsprotocol.types import (
    TEXT_DOCUMENT_CODE_ACTION,
    TEXT_DOCUMENT_COMPLETION,
    TEXT_DOCUMENT_DID_OPEN,
    TEXT_DOCUMENT_DID_CHANGE,
    WORKSPACE_DID_CHANGE_WATCHED_FILES,
    CodeAction,
    CodeActionKind,
    CodeActionOptions,
    CodeActionParams,
    CompletionItem,
    CompletionOptions,
    CompletionParams,
    DidChangeTextDocumentParams,
    DidChangeWatchedFilesParams,
    DidOpenTextDocumentParams,
    Diagnostic,
    Position,
    PublishDiagnosticsParams,
    Range,
    TextEdit,
    WorkspaceEdit,
)
from pygls.lsp.server import LanguageServer

from aeon.facade.driver import AeonDriver
from aeon.sugar.parser import parse_main_program
from aeon.sugar.program import (
    Definition,
    SAbstraction,
    SAnnotation,
    SApplication,
    SHole,
    SIf,
    SLet,
    SRec,
    STerm,
    STypeAbstraction,
    STypeApplication,
)
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.location import FileLocation
from aeon.utils.name import Name
from aeon.utils.pprint import pretty_print_sterm


@dataclass
class ParsedHole:
    hole_name: str
    range: Range


@dataclass
class HoleActionData:
    function_name: Name
    hole_name: Name
    range: Range

    @property
    def title(self) -> str:
        return f"Synthesize ?{self.hole_name.pretty()} in {self.function_name.pretty()}"


class AeonLanguageServer(LanguageServer):
    def __init__(self, aeon_driver: AeonDriver):
        super().__init__("aeon.lsp.server", "0.1.0")
        self.aeon_driver = aeon_driver
        self.debounce_delay = 0.3
        self._driver_lock = asyncio.Lock()
        self._silent_ui = SilentSynthesisUI()
        self._setup_handlers()

    def start(self, tcp_server):
        if not tcp_server:
            self.start_io()

        host, port = tcp_server.split(":") if ":" in tcp_server else ("localhost", tcp_server)

        print(f"Listening on {host}:{port}")
        self.start_tcp(host, int(port))

    @staticmethod
    def _uri_to_path(uri: str) -> str:
        parsed = urlparse(uri)
        if parsed.scheme != "file":
            return uri

        path = unquote(parsed.path or "")
        if parsed.netloc:
            netloc = parsed.netloc
            if not path.startswith("/"):
                path = "/" + path
            path = f"/{netloc}{path}"
        return path or uri

    @staticmethod
    def _position_before(a: Position, b: Position) -> bool:
        return (a.line < b.line) or (a.line == b.line and a.character < b.character)

    @staticmethod
    def _position_before_or_equal(a: Position, b: Position) -> bool:
        return (a.line < b.line) or (a.line == b.line and a.character <= b.character)

    @staticmethod
    def _is_empty_range(range_: Range) -> bool:
        return range_.start.line == range_.end.line and range_.start.character == range_.end.character

    @classmethod
    def _ranges_overlap(cls, a: Range, b: Range) -> bool:
        if cls._is_empty_range(b):
            return cls._position_before_or_equal(a.start, b.start) and cls._position_before(b.start, a.end)
        if cls._is_empty_range(a):
            return cls._position_before_or_equal(b.start, a.start) and cls._position_before(a.start, b.end)
        return cls._position_before(a.start, b.end) and cls._position_before(b.start, a.end)

    def _collect_hole_candidates(self, source: str, filename: str) -> Dict[str, List[ParsedHole]]:
        try:
            program = parse_main_program(source, filename=filename)
        except Exception as exc:  # pragma: no cover - defensive logging
            self.logger.debug("Failed to parse program for code actions: %s", exc)
            return {}

        holes_by_function: Dict[str, List[ParsedHole]] = {}
        for definition in program.definitions:
            if not isinstance(definition, Definition):
                continue

            collected: List[ParsedHole] = []
            self._collect_holes_from_term(definition.body, collected)
            if collected:
                holes_by_function[definition.name.pretty()] = collected

        return holes_by_function

    def _collect_holes_from_term(self, term: STerm, acc: List[ParsedHole]) -> None:
        if isinstance(term, SHole):
            loc = getattr(term, "loc", None)
            if isinstance(loc, FileLocation):
                start_line, start_char = loc.get_start()
                end_line, end_char = loc.get_end()
                range_ = Range(
                    start=Position(line=max(0, start_line - 1), character=max(0, start_char - 1)),
                    end=Position(line=max(0, end_line - 1), character=max(0, end_char - 1)),
                )
                acc.append(ParsedHole(term.name.pretty(), range_))
            return

        if isinstance(term, SAnnotation):
            self._collect_holes_from_term(term.expr, acc)
        elif isinstance(term, SApplication):
            self._collect_holes_from_term(term.fun, acc)
            self._collect_holes_from_term(term.arg, acc)
        elif isinstance(term, SAbstraction):
            self._collect_holes_from_term(term.body, acc)
        elif isinstance(term, SLet):
            self._collect_holes_from_term(term.var_value, acc)
            self._collect_holes_from_term(term.body, acc)
        elif isinstance(term, SRec):
            self._collect_holes_from_term(term.var_value, acc)
            self._collect_holes_from_term(term.body, acc)
        elif isinstance(term, SIf):
            self._collect_holes_from_term(term.cond, acc)
            self._collect_holes_from_term(term.then, acc)
            self._collect_holes_from_term(term.otherwise, acc)
        elif isinstance(term, STypeApplication):
            self._collect_holes_from_term(term.body, acc)
        elif isinstance(term, STypeAbstraction):
            self._collect_holes_from_term(term.body, acc)

    async def _prepare_hole_actions(
        self,
        source: str,
        filename: str,
        holes_by_function: Dict[str, List[ParsedHole]],
    ) -> List[HoleActionData]:
        if not holes_by_function:
            return []

        loop = asyncio.get_running_loop()
        parse_errors = await loop.run_in_executor(
            None,
            partial(self.aeon_driver.parse, filename=filename, aeon_code=source),
        )
        if parse_errors:
            return []

        has_holes = await loop.run_in_executor(None, self.aeon_driver.has_synth)
        if not has_holes:
            return []

        driver_map: Dict[str, Tuple[Name, List[Name]]] = {
            fun.pretty(): (fun, holes) for fun, holes in self.aeon_driver.incomplete_functions
        }

        hole_actions: List[HoleActionData] = []
        for func_name, parsed_holes in holes_by_function.items():
            driver_entry = driver_map.get(func_name)
            if not driver_entry:
                continue

            function_name, driver_holes = driver_entry
            sorted_parsed = sorted(parsed_holes, key=lambda h: (h.range.start.line, h.range.start.character))

            if len(sorted_parsed) != len(driver_holes):
                continue

            for parsed_hole, driver_hole in zip(sorted_parsed, driver_holes):
                hole_actions.append(
                    HoleActionData(
                        function_name=function_name,
                        hole_name=driver_hole,
                        range=parsed_hole.range,
                    )
                )

        return hole_actions

    async def _build_code_action_for_hole(self, uri: str, hole: HoleActionData) -> Optional[CodeAction]:
        loop = asyncio.get_running_loop()

        def run_synthesis():
            _, mapping = self.aeon_driver.synthesize_targets(
                targets=[(hole.function_name, [hole.hole_name])],
                synthesis_ui=self._silent_ui,
                display_results=False,
            )
            return mapping.get(hole.hole_name)

        try:
            synthesized = await loop.run_in_executor(None, run_synthesis)
        except Exception as exc:  # pragma: no cover - synthesis failures are logged
            self.logger.debug("Synthesis failed for hole %s: %s", hole.hole_name.pretty(), exc)
            return None

        if synthesized is None:
            return None

        replacement = pretty_print_sterm(synthesized)
        edit = TextEdit(range=hole.range, new_text=replacement)

        return CodeAction(
            title=hole.title,
            kind=CodeActionKind.QuickFix,
            edit=WorkspaceEdit(changes={uri: [edit]}),
        )

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

        @self.feature(TEXT_DOCUMENT_CODE_ACTION, CodeActionOptions(code_action_kinds=[CodeActionKind.QuickFix]))
        async def code_action(
            ls: AeonLanguageServer,
            params: CodeActionParams,
        ) -> Optional[List[CodeAction]]:
            return await ls.code_action_handler(params)

    async def code_action_handler(self, params: CodeActionParams) -> Optional[List[CodeAction]]:
        document = self.workspace.get_text_document(params.text_document.uri)
        if document is None:
            return []

        filename = self._uri_to_path(params.text_document.uri)
        holes_by_function = self._collect_hole_candidates(document.source, filename)
        if not holes_by_function:
            return []

        actions: List[CodeAction] = []

        # 2. Synthesis actions
        async with self._driver_lock:
            hole_actions = await self._prepare_hole_actions(document.source, filename, holes_by_function)

            relevant_holes = [hole for hole in hole_actions if self._ranges_overlap(hole.range, params.range)]

            for hole in relevant_holes:
                action = await self._build_code_action_for_hole(params.text_document.uri, hole)
                if action is not None:
                    actions.append(action)

        return actions

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
