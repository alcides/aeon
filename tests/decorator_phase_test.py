from __future__ import annotations

from aeon.logger.logger import setup_logger
from aeon.utils.name import Name

from tests.driver import check_and_return_core

setup_logger()


def test_core_phase_decorator_runs_after_typecheck():
    source = """
        @after_typecheck
        def f(x: Int) : Int = x + 1;
        def main (x:Int) : Int = f(x);
    """
    _, _, _, metadata = check_and_return_core(source)
    f_entries = [v for k, v in metadata.items() if isinstance(k, Name) and k.name == "f" and isinstance(v, dict)]
    assert any(v.get("ran_after_typecheck") is True for v in f_entries)


def test_sugar_phase_decorator_still_runs_before_elaboration():
    source = r"""
        @csv_data("1.0,2.0\n3.0,4.0")
        def f(x:Float) : Float = x
        def main (x:Int) : Int = 1;
    """
    _, _, _, metadata = check_and_return_core(source)
    assert any("goals" in v for v in metadata.values() if isinstance(v, dict))
