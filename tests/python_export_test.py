from __future__ import annotations

import dataclasses
from pathlib import Path

import pytest

from aeon.backend.evaluator import eval as aeon_eval
from aeon.backend.python_export import PythonExportError, find_binding
from aeon.core.terms import Application, Let, Literal, Rec, Term, Var
from aeon.core.types import t_int
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SynthesisFormat
from aeon.synthesis.uis.terminal import TerminalUI

EXAMPLES = Path(__file__).resolve().parent.parent / "examples"


def _driver(budget: int = 1) -> AeonDriver:
    cfg = AeonConfig(
        synthesizer="tdsyn_enumerative",
        synthesis_ui=TerminalUI(),
        synthesis_budget=budget,
        no_main=True,
        synthesis_format=SynthesisFormat.DEFAULT,
    )
    return AeonDriver(cfg)


def _export(source: str, fun_name: str) -> str:
    driver = _driver()
    errors = list(driver.parse(filename=None, aeon_code=source))
    assert errors == [], errors
    return driver.export(fun_name)


def _run(source: str, fun_name: str):
    """Export a function, exec the generated Python, and return the callable."""
    code = _export(source, fun_name)
    ns: dict = {}
    exec(code, ns)
    return ns[fun_name]


def test_export_bundles_dependencies():
    src = (
        "def inc (x:Int) : Int := x + 1;\ndef twice (x:Int) : Int := inc (inc x);\ndef unused (x:Int) : Int := x - 1;\n"
    )
    code = _export(src, "twice")
    # The transitive dependency is pulled in, the unrelated one is dropped.
    assert "def inc(" in code
    assert "unused" not in code
    assert _run(src, "twice")(5) == 7


def test_export_keeps_native_import_even_if_not_referenced_in_ast():
    # ``sq`` mentions ``math`` only inside a native string, so the import must
    # be force-included for the export to be runnable.
    src = 'def math : Unit := native_import "math";\ndef sq (x:Float) : Float := native "math.sqrt(x)";\n'
    code = _export(src, "sq")
    assert "math = __import__('math')" in code
    ns: dict = {}
    exec(code, ns)
    assert ns["sq"](16.0) == 4.0


def test_export_simple_arithmetic():
    src = "def double (x:Int) : Int := x + x;"
    code = _export(src, "double")
    assert "def double(x):" in code
    assert _run(src, "double")(21) == 42


def test_export_if_is_ternary():
    src = "def clamp (x:Int) : Int := if x < 0 then 0 else x;"
    code = _export(src, "clamp")
    assert "if" in code and "else" in code
    fn = _run(src, "clamp")
    assert fn(-5) == 0
    assert fn(7) == 7


def test_export_recursion():
    src = "def fib (n:Int) : Int := if n < 2 then n else fib (n - 1) + fib (n - 2);"
    fn = _run(src, "fib")
    assert fn(10) == 55


def test_export_multi_arg_is_curried():
    src = "def add (x:Int) (y:Int) : Int := x + y;"
    code = _export(src, "add")
    assert "lambda y" in code
    assert _run(src, "add")(3)(4) == 7


def test_export_string_literal_inlined():
    src = "def tag (s:String) : String := s;"
    fn = _run(src, "tag")
    assert fn("hello") == "hello"


def test_export_boolean_operators():
    src = "def both (a:Bool) (b:Bool) : Bool := a && b;"
    fn = _run(src, "both")
    assert fn(True)(True) is True
    assert fn(True)(False) is False


def test_export_native_string_inlined():
    src = 'def mylen (xs:String) : Int := native "len(xs)";'
    code = _export(src, "mylen")
    assert "len(xs)" in code
    assert _run(src, "mylen")("abcd") == 4


def test_export_runs_synthesis_to_fill_holes():
    # ``f`` is defined with a hole. Exporting it must run synthesis first, so
    # the emitted Python contains the synthesized result and no unfilled '?'.
    src = "def f (x:Int) : {y:Int | y = x} := ?h;\n"
    driver = _driver(budget=3)
    assert list(driver.parse(filename=None, aeon_code=src)) == []
    code = driver.export("f")
    assert "def f(x):" in code
    assert "?" not in code  # the hole was replaced by the synthesized term


def test_export_unknown_function_raises():
    src = "def double (x:Int) : Int := x + x;"
    driver = _driver()
    assert list(driver.parse(filename=None, aeon_code=src)) == []
    with pytest.raises(PythonExportError):
        driver.export("nonexistent")


# --- Cross-check: exported Python matches the Aeon interpreter ---------------


def _replace_tail(core, new_tail):
    """Swap the innermost body of the top-level binding chain so the program
    evaluates to ``new_tail`` instead of ``main``."""
    if isinstance(core, (Rec, Let)):
        return dataclasses.replace(core, body=_replace_tail(core.body, new_tail))
    return new_tail


def _eval_with_aeon(driver: AeonDriver, fun_name: str, args: list[int]) -> object:
    """Apply ``fun_name`` to integer ``args`` and evaluate it with the Aeon
    interpreter, reusing the program's own top-level bindings."""
    binding = find_binding(driver.core, fun_name)
    assert binding is not None
    name, _ = binding
    call: Term = Var(name)
    for a in args:
        call = Application(call, Literal(a, t_int))
    program = _replace_tail(driver.core, call)
    return aeon_eval(program, driver.evaluation_ctx)


def _eval_with_python(driver: AeonDriver, fun_name: str, args: list[int]) -> object:
    """Export ``fun_name`` to Python, exec it, and apply it (curried) to ``args``."""
    ns: dict = {}
    exec(driver.export(fun_name), ns)
    fn = ns[fun_name]
    for a in args:
        fn = fn(a)
    return fn


# (example file, function, argument list) — small, self-contained functions
# drawn from the examples/ folder, covering recursion, currying, nested
# conditionals and inlined ``native`` strings.
EXPORT_EXAMPLES = [
    ("fibonacci.ae", "fib", [10]),
    ("factorial.ae", "factorial", [5]),
    ("syntax/mult.ae", "mult2", [6, 7]),
    ("syntax/mult.ae", "mult4", [6, 7]),
    ("syntax/maxI.ae", "maxI", [3, 9]),
    ("syntax/ackermann.ae", "ack", [2, 3]),
]


@pytest.mark.parametrize("filename,fun_name,args", EXPORT_EXAMPLES)
def test_exported_python_matches_aeon(filename: str, fun_name: str, args: list[int]):
    driver = _driver()
    errors = list(driver.parse(filename=str(EXAMPLES / filename)))
    assert errors == [], errors

    aeon_result = _eval_with_aeon(driver, fun_name, args)
    python_result = _eval_with_python(driver, fun_name, args)
    assert python_result == aeon_result
