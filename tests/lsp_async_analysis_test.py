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


def test_stale_synthesis_cannot_replace_newer_type_cache(monkeypatch):
    from aeon.core.terms import Rec, Let
    from aeon.synthesis import entrypoint

    ls = make_server()
    uri = "file:///stale-synthesis-cache.ae"
    first = "def marker:Int := 1; def f(x:Int):Int := ?hole;"
    second = "def marker:Bool := true; def f(x:Int):Int := ?hole;"
    put(ls, uri, first)
    started, release = threading.Event(), threading.Event()
    real_driver = server.AeonDriver

    def blocking_driver(cfg):
        driver = real_driver(cfg)
        original = driver.parse

        def parse(*args, **kwargs):
            errors = original(*args, **kwargs)
            started.set()
            assert release.wait(20)
            return errors

        driver.parse = parse
        return driver

    def marker_type():
        node = aeon_adapter.get_core(uri)
        while isinstance(node, (Rec, Let)):
            if node.var_name.name == "marker":
                return str(node.var_type).strip()
            node = node.body
        raise AssertionError("missing marker")

    monkeypatch.setattr(server, "AeonDriver", blocking_driver)
    monkeypatch.setattr(entrypoint, "synthesize_holes", lambda *a, **kw: {})
    monkeypatch.setattr(server, "_emit_synthesis_pending", lambda *args: None)
    monkeypatch.setattr(ls, "window_show_message", lambda *args: None)

    async def run():
        assert not (await aeon_adapter.parse(ls, uri)).diagnostics
        task = asyncio.create_task(ls.protocol.fm.commands[server.SYNTHESIZE_COMMAND](uri, "hole", "smt", 1))
        try:
            assert await asyncio.to_thread(started.wait, 20)
            put(ls, uri, second, version=2)
            aeon_adapter.clear_cache(uri)
            assert not (await aeon_adapter.parse(ls, uri)).diagnostics
            assert marker_type() == "Bool"
        finally:
            release.set()
        await task
        await aeon_adapter.parse(ls, uri)
        assert marker_type() == "Bool"

    asyncio.run(run())


def test_z3_recovery_rebuilds_execution_state_from_worker_snapshot(monkeypatch):
    from z3.z3types import Z3Exception
    from aeon.verification.constructor_registry import ConstructorRegistry

    ls = make_server()
    uri = "file:///worker-snapshot-recovery.ae"
    source = "import List; @llvm def id(x:Int):Int := x; def f:Int := ?hole;"
    put(ls, uri, source)
    messages = []
    monkeypatch.setattr(ls, "window_show_message", lambda params: messages.append(params.message))

    async def run():
        assert not (await aeon_adapter.parse(ls, uri)).diagnostics
        driver = AeonDriver(ls.aeon_driver.cfg)

        def fail(*args, **kwargs):
            raise Z3Exception("simulated solver failure")

        monkeypatch.setattr(driver, "parse", fail)
        result = await asyncio.to_thread(server._run_synthesis, driver, ls, uri, "hole", "smt", 1, source)
        assert result is not None, messages
        assert driver.evaluation_ctx is not None
        assert driver.constructor_names
        assert driver.session.state(ConstructorRegistry).groups
        assert not any("Synthesis failed" in message for message in messages)

    asyncio.run(run())


@pytest.mark.parametrize("related", [False, True])
def test_synthesis_only_discarded_for_its_actual_dependencies(monkeypatch, tmp_path, related):
    ls = make_server()
    uri = (tmp_path / "Main.ae").as_uri()
    dependency = tmp_path / "Dependency.ae"
    put(ls, uri, "def f:Int := ?hole;")
    started, release = threading.Event(), threading.Event()
    edits = []

    def synthesize(driver, *_args, **_kwargs):
        # Include a dependency first discovered by this request, before any
        # editor analysis has populated the dependency cache for this URI.
        driver.session.source_paths.add(str(dependency))
        started.set()
        assert release.wait(10)
        return "42", Range(Position(0, 13), Position(0, 18))

    monkeypatch.setattr(server, "_run_synthesis", synthesize)
    monkeypatch.setattr(server, "_emit_synthesis_pending", lambda *args: None)
    monkeypatch.setattr(ls, "window_show_message", lambda *args: None)
    monkeypatch.setattr(ls, "workspace_apply_edit", edits.append)

    async def run():
        task = asyncio.create_task(ls.protocol.fm.commands[server.SYNTHESIZE_COMMAND](uri, "hole", "smt", 1))
        try:
            assert await asyncio.to_thread(started.wait, 10)
            aeon_adapter.clear_cache((dependency if related else tmp_path / "Unrelated.ae").as_uri())
        finally:
            release.set()
        await task

    asyncio.run(run())
    assert bool(edits) is not related


def test_superseded_analyses_are_coalesced_before_worker_submission(monkeypatch):
    import dill
    from concurrent.futures import ThreadPoolExecutor
    from aeon.lsp import analysis

    ls = make_server()
    uri = "file:///coalesced-analysis.ae"
    put(ls, uri, "old")
    started, release = threading.Event(), threading.Event()
    seen = []

    def analyze(source, *_args):
        seen.append(source)
        if source == "old":
            started.set()
            assert release.wait(10)
        return dill.dumps((aeon_adapter.ParseResult([]), {"proofs": [{"source": source}]}, set()))

    monkeypatch.setattr(analysis, "_analyze", analyze)

    async def run():
        tasks = [asyncio.create_task(aeon_adapter.parse(ls, uri))]
        try:
            assert await asyncio.to_thread(started.wait, 10)
            for version, source in enumerate(["intermediate", "latest"], start=2):
                put(ls, uri, source, version)
                aeon_adapter.clear_cache(uri)
                tasks.append(asyncio.create_task(aeon_adapter.parse(ls, uri)))
                await asyncio.sleep(0)
                await asyncio.sleep(0)
            assert seen == ["old"]
        finally:
            release.set()
        await asyncio.gather(*tasks)
        assert seen == ["old", "latest"]
        assert aeon_adapter.get_proof_obligations(uri) == [{"source": "latest"}]

    with ThreadPoolExecutor(max_workers=1) as executor:
        monkeypatch.setattr(analysis, "_executor", executor)
        asyncio.run(run())
