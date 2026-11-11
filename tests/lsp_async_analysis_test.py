"""Editor analysis and synthesis must respect document lifetimes."""

import asyncio
import threading
from types import SimpleNamespace

import pytest
from lsprotocol.types import Position, Range, TextDocumentItem
from pygls.workspace import Workspace

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.lsp import aeon_adapter, server
from aeon.synthesis.uis.api import SilentSynthesisUI


def make_server():
    ls = server.AeonLanguageServer(AeonDriver(AeonConfig("random_search", SilentSynthesisUI(), 0)))
    ls.protocol._workspace = Workspace(None)
    ls.debounce_delay = 0
    return ls


def put(ls, uri, source, version=1):
    ls.workspace.put_text_document(TextDocumentItem(uri=uri, language_id="aeon", version=version, text=source))


def test_real_compilation_keeps_the_event_loop_responsive():
    ls = make_server()
    uri = "file:///responsive-review.ae"
    put(ls, uri, "import List; import Array; import Math; def main(u:Int):Int := 1;")
    aeon_adapter.clear_cache(uri)

    async def run():
        task = asyncio.create_task(aeon_adapter.parse(ls, uri))
        await asyncio.sleep(0)
        await asyncio.sleep(0.01)
        assert not task.done(), "compiler analysis ran synchronously on the event loop"
        result = await task
        assert not result.diagnostics
        assert aeon_adapter.get_core(uri) is not None
        assert aeon_adapter.get_type_index(uri) is not None

    asyncio.run(run())


@pytest.mark.parametrize("unsaved", [False, True])
def test_dependency_change_invalidates_importer_diagnostics(tmp_path, monkeypatch, unsaved):
    monkeypatch.chdir(tmp_path)
    library = tmp_path / "Dependency.ae"
    library.write_text("def value:Int := 1;")
    uri = (tmp_path / "Main.ae").as_uri()
    ls = make_server()
    put(ls, uri, "import Dependency; def main(u:Int):Int := Dependency.value;")

    async def run():
        assert not (await aeon_adapter.parse(ls, uri)).diagnostics
        if unsaved:
            put(ls, library.as_uri(), "def value:Bool := true;")
        else:
            library.write_text("def value:Bool := true;")
        assert uri in aeon_adapter.clear_cache(library.as_uri())
        result = await aeon_adapter.parse(ls, uri)
        assert result.diagnostics
        assert any("Bool" in diagnostic.message for diagnostic in result.diagnostics)

    asyncio.run(run())


def test_missing_dependency_is_reanalyzed_when_created(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    library = tmp_path / "NewLibrary.ae"
    uri = (tmp_path / "Main.ae").as_uri()
    ls = make_server()
    put(ls, uri, "import NewLibrary; def main(u:Int):Int := NewLibrary.value;")

    async def run():
        assert (await aeon_adapter.parse(ls, uri)).diagnostics
        library.write_text("def value:Int := 1;")
        assert uri in aeon_adapter.clear_cache(library.as_uri())
        assert not (await aeon_adapter.parse(ls, uri)).diagnostics

    asyncio.run(run())


@pytest.mark.parametrize("changed", [False, True])
def test_synthesis_applies_only_to_the_captured_document_version(monkeypatch, changed):
    ls = make_server()
    uri, source = "file:///versioned-review.ae", "def f:Int := ?hole;"
    put(ls, uri, source)
    started, release = threading.Event(), threading.Event()
    edits, messages = [], []

    def synthesize(driver, _ls, _uri, *_args, **kwargs):
        assert driver is not ls.aeon_driver
        assert kwargs["source"] == source
        started.set()
        assert release.wait(5)
        offset = source.index("?hole")
        return "42", Range(Position(0, offset), Position(0, offset + 5))

    monkeypatch.setattr(server, "_run_synthesis", synthesize)
    monkeypatch.setattr(server, "_emit_synthesis_pending", lambda *args: None)
    monkeypatch.setattr(ls, "workspace_apply_edit", lambda params: edits.append(params.edit))
    monkeypatch.setattr(ls, "window_show_message", messages.append)

    async def run():
        task = asyncio.create_task(ls.protocol.fm.commands[server.SYNTHESIZE_COMMAND](uri, "hole", "random_search"))
        assert await asyncio.to_thread(started.wait, 5)
        if changed:
            put(ls, uri, "# new line\n" + source, version=2)
        release.set()
        await task

    asyncio.run(run())
    if changed:
        assert not edits
        assert any("discarded" in message.message for message in messages)
    else:
        assert edits[0].changes is None
        document_edit = edits[0].document_changes[0]
        assert document_edit.text_document.version == 1
        assert document_edit.edits[0].new_text == "42"


def test_obsolete_analysis_is_not_published(monkeypatch):
    from aeon.lsp import analysis

    uri = "file:///obsolete-review.ae"
    document = SimpleNamespace(source="old")
    ls = SimpleNamespace(
        aeon_driver=AeonDriver(AeonConfig("random_search", SilentSynthesisUI(), 0)),
        workspace=SimpleNamespace(get_text_document=lambda _: document),
    )
    aeon_adapter.clear_cache(uri)

    async def run():
        started, release = asyncio.Event(), asyncio.Event()
        seen = []

        async def analyze(source, _config, _uri):
            seen.append(source)
            if source == "old":
                started.set()
                await release.wait()
            return aeon_adapter.ParseResult([]), {"proofs": [{"source": source}]}, set()

        monkeypatch.setattr(analysis, "analyze", analyze)
        task = asyncio.create_task(aeon_adapter.parse(ls, uri))
        await started.wait()
        document.source = "new"
        aeon_adapter.clear_cache(uri)
        release.set()
        await task
        assert seen == ["old", "new"]
        assert aeon_adapter.get_proof_obligations(uri) == [{"source": "new"}]

    asyncio.run(run())
