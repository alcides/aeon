import sys

# Aeon elaborates a whole program (every imported library's definitions) into
# one deeply-nested let-chain and walks it recursively, so the stack depth
# grows with the total number of definitions in scope. A program that opens
# the larger libraries (e.g. ``Learning`` with the full scikit-learn estimator
# family, transitively pulling in ``Math`` / ``List`` / ``Tensor`` …) exceeds
# CPython's default limit of 1000 — especially under pytest's ``beartype``
# wrapping, which adds stack frames per call. The CLI entry point
# (``aeon/__main__.py``) already raised this; doing it here means every
# ``import aeon`` (tests, library use, the LSP) gets the same headroom.
sys.setrecursionlimit(max(sys.getrecursionlimit(), 10000))
