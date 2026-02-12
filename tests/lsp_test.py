from unittest.mock import MagicMock, AsyncMock, patch, PropertyMock
from aeon.lsp.server import AeonLanguageServer
from lsprotocol.types import CodeActionParams, Range, Position, TextDocumentIdentifier, CodeActionContext
import asyncio


def test_code_action_replace_hole_with_3():
    asyncio.run(run_test_code_action_replace_hole_with_3())


async def run_test_code_action_replace_hole_with_3():
    # Setup
    with patch("aeon.lsp.server.LanguageServer.workspace", new_callable=PropertyMock) as mock_workspace_prop:
        # Configure the mock property to return our mock workspace
        mock_workspace = MagicMock()
        mock_workspace_prop.return_value = mock_workspace

        server = AeonLanguageServer(MagicMock())

        source = """
        def test : {x:Int | x == 42} = ?hole;
        """

        document = MagicMock()
        document.source = source
        document.uri = "file:///test.ae"
        mock_workspace.get_text_document.return_value = document

        # Mock the driver lock
        server._driver_lock = AsyncMock()
        server._driver_lock.__aenter__.return_value = None
        server._driver_lock.__aexit__.return_value = None

        # Params
        params = CodeActionParams(
            text_document=TextDocumentIdentifier(uri="file:///test.ae"),
            range=Range(start=Position(line=1, character=21), end=Position(line=1, character=26)),
            context=CodeActionContext(diagnostics=[]),
        )

        # Mock _prepare_hole_actions to return a hole action
        hole_data = MagicMock()
        hole_data.hole_name = MagicMock()
        hole_data.hole_name.pretty.return_value = "hole"
        hole_data.function_name = MagicMock()
        hole_data.function_name.pretty.return_value = "test"
        hole_data.range = Range(start=Position(line=1, character=21), end=Position(line=1, character=26))
        hole_data.title = "Synthesize ?hole in test"

        server._prepare_hole_actions = AsyncMock(return_value=[hole_data])

        server.aeon_driver.synthesize_targets = MagicMock(return_value=(None, {hole_data.hole_name: MagicMock()}))
        with patch("aeon.lsp.server.pretty_print_sterm", return_value="42"):
            actions = await server.code_action_handler(params)

        assert actions is not None
        assert len(actions) > 0

        # Check for Synthesis action
        synth_action = next((a for a in actions if "Synthesize" in a.title), None)
        assert synth_action is not None
        assert synth_action.edit.changes["file:///test.ae"][0].new_text == "42"
