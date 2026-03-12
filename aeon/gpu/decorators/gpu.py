from __future__ import annotations

from aeon.decorators.api import Metadata, metadata_update
from aeon.sugar.program import Definition, STerm


def gpu(
    args: list[STerm],
    fun: Definition,
    metadata: Metadata,
) -> tuple[Definition, list[Definition], Metadata]:
    assert len(args) == 0, "gpu decorator expects zero arguments"
    metadata = metadata_update(metadata, fun, {"gpu": True})
    return fun, [], metadata
