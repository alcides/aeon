"""Incremental decorator handling while editing in the IDE."""

from __future__ import annotations

import tempfile

import pytest

from aeon.compilation.compile import clear_unit_cache, compile_and_link_program
from aeon.facade.api import UnknownDecoratorError

PROGRAM = """def double (n:Int) : {x:Int | x = 2 * n} :=
    ?h
"""


def _compile_with_decorator(decorator_line: str) -> tuple[list, bool]:
    clear_unit_cache()
    source = f"{decorator_line}\n{PROGRAM}"
    with tempfile.NamedTemporaryFile(mode="w", suffix=".ae", delete=False, encoding="utf-8") as tmp:
        tmp.write(source)
        path = tmp.name
    _unit, _core, _ctx, _meta, _trusted, errors = compile_and_link_program(
        source, filename=path, is_main=True, is_main_hole=False, use_cache=False
    )
    return errors, _core is not None


@pytest.mark.parametrize(
    "decorator_line",
    [
        "@e",
        "@exa",
        "@exam",
        "@exampl",
        "@example",
        "@example(double 3 = 6)",
    ],
)
def test_partial_example_decorator_does_not_crash(decorator_line: str):
    errors, ok = _compile_with_decorator(decorator_line)
    assert ok
    assert not any(isinstance(e, UnknownDecoratorError) for e in errors)


def test_unknown_decorator_still_errors():
    errors, ok = _compile_with_decorator("@not_a_decorator")
    assert not ok
    assert any(isinstance(e, UnknownDecoratorError) for e in errors)
