"""Isolated compiler worker for editor diagnostics.

Only analysis snapshots cross the process boundary; solver sessions and LLVM
engines stay in the worker. A persistent spawned process avoids both blocking
the event loop and concurrent access to Z3's default context.
"""

from __future__ import annotations

import asyncio
import io
import os
from concurrent.futures import ProcessPoolExecutor
from dataclasses import replace
from multiprocessing import get_context
from pathlib import Path

import dill

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI

_executor: ProcessPoolExecutor | None = None


def _analyze(source: str, config: AeonConfig, uri: str, directory: str) -> bytes:
    from aeon.lsp import aeon_adapter as adapter

    os.chdir(directory)
    driver = AeonDriver(replace(config, check_only=True, synthesis_ui=SilentSynthesisUI()))
    try:
        result = asyncio.run(adapter._parse(io.StringIO(source), driver, uri))
        snapshot = {key: cache.get(uri) for key, cache in adapter.analysis_caches().items()}
        dependencies = adapter._dependencies.get(uri, set()) | {Path(p).as_uri() for p in driver.session.source_paths}
        return dill.dumps((result, snapshot, dependencies))
    finally:
        # The parent owns last-good editor state. Do not accumulate open files
        # or obsolete analysis trees in the long-lived compiler process.
        for cache in adapter.analysis_caches().values():
            cache.pop(uri, None)
        adapter._dependencies.pop(uri, None)


async def analyze(source: str, config: AeonConfig, uri: str):
    global _executor
    if _executor is None:
        _executor = ProcessPoolExecutor(max_workers=1, mp_context=get_context("spawn"))
    config = replace(config, synthesis_ui=SilentSynthesisUI())
    payload = await asyncio.get_running_loop().run_in_executor(_executor, _analyze, source, config, uri, os.getcwd())
    return dill.loads(payload)
