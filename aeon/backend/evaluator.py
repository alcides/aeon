"""Runtime evaluator — pure re-export of the Rust core
(``aeon-rs/src/evaluator.rs``).

The native FFI escape hatch (``native "expr"``) still goes through
Python's builtin ``eval`` — that's what evaluates the Python source
inside the string, which Rust calls back into via ``builtins.eval``.
"""

from __future__ import annotations

from aeon_rs import EvaluationContext as EvaluationContext
from aeon_rs import eval as eval
