"""Unit tests for ``@example`` I/O extraction used by Contata/AFTA."""

from aeon.sugar.parser import parse_program
from aeon.synthesis.decorators import _extract_io_example, _list_literal_value


def _assertion_from(src: str):
    prog = parse_program(src)
    defn = next(d for d in prog.definitions if d.name.name == "f")
    return defn.decorators[0].macro_args[0], defn.name


def test_extract_scalar_io():
    assertion, name = _assertion_from(
        """
@example(f 3 = 9)
def f (x: Int) : Int := 0;
"""
    )
    assert _extract_io_example(assertion, name) == ([3], 9)


def test_extract_list_literal_io():
    assertion, name = _assertion_from(
        """
import List
@example(f [1, 2, 3] = 3)
def f (xs: (List Int)) : Int := 0;
"""
    )
    assert _extract_io_example(assertion, name) == ([(1, 2, 3)], 3)


def test_extract_empty_list_literal_io():
    assertion, name = _assertion_from(
        """
import List
@example(f [] = 0)
def f (xs: (List Int)) : Int := 0;
"""
    )
    assert _extract_io_example(assertion, name) == ([()], 0)


def test_list_literal_value_helper():
    assertion, _name = _assertion_from(
        """
import List
@example(f [7] = 1)
def f (xs: (List Int)) : Int := 0;
"""
    )
    # assertion is (== (f [7]) 1); the list is the call argument
    call = assertion.fun.arg
    lst = call.arg
    assert _list_literal_value(lst) == (7,)


def test_extract_io_accepts_module_prefixed_call():
    """``open List`` can rebind ``f`` in examples to ``List_f``-style names."""
    from aeon.utils.name import Name
    from aeon.sugar.program import SApplication, SVar

    assertion, _ = _assertion_from(
        """
import List
@example(f [] = 0)
def f (xs: (List Int)) : Int := 0;
"""
    )
    call = assertion.fun.arg
    lit = assertion.arg
    op = assertion.fun.fun
    prefixed = SApplication(SVar(Name("List_f", 0)), call.arg)
    rewritten = SApplication(SApplication(op, prefixed), lit)
    assert _extract_io_example(rewritten, Name("f", 0)) == ([()], 0)
