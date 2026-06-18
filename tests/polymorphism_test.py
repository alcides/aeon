from __future__ import annotations

from aeon.sugar.parser import parse_type
from aeon.utils.name import Name

from tests.driver import check_compile_expr

# The recursion limit is raised centrally in ``aeon/__init__.py`` (importing
# aeon sets it to >= 10000). This module used to lower it to 1500 at import
# time, which — now that the bundled libraries are larger — starved later
# tests (e.g. ``learning_test``) of stack and made them fail with
# RecursionError.


def tt(e: str, t: str, vars: None | dict[str, str] = None):
    vs = {Name(k): parse_type(v) for (k, v) in vars.items()} if vars is not None else None
    return check_compile_expr(e, parse_type(t), extra_vars=vs)


def test_simple_def():
    assert tt("let k : Int := 1 in k", "Int")


def test_poly():
    assert tt(
        """ let max : forall a:B, (x:a) -> (y:a) -> {z:a| (z = x) || (z = y)  } := Λa:B => (fun x => fun y => if x < y then y else x) in
            let r := max 0 5 in
            let vvv : {m:Int | 0 <= m} := r + 1 in
            true""",
        """Bool""",
    )
