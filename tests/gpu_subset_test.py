import pytest

from aeon.core.terms import Literal, Application, Var, Let, If, Rec
from aeon.core.types import t_int, t_float, t_bool, TypeConstructor
from aeon.gpu.gpu_converter import GInt, GFloat, GBool
from aeon.gpu.pipeline import compile_to_gpu
from aeon.utils.name import Name


def test_unary_minus_int():
    term = Let(Name("x"), Application(Var(Name("-")), Literal(5, t_int)), Var(Name("x")))
    ir = compile_to_gpu(term, Name("kernel"), [Name("input")], [GInt])
    assert "TODO" in ir


def test_unary_minus_float():
    term = Let(Name("x"), Application(Var(Name("-")), Literal(5.0, t_float)), Var(Name("x")))
    ir = compile_to_gpu(term, Name("kernel"), [Name("input")], [GFloat])
    assert "TODO" in ir


def test_binary_minus():
    term = Let(
        Name("x"), Application(Application(Var(Name("-")), Literal(5, t_int)), Literal(3, t_int)), Var(Name("x"))
    )
    ir = compile_to_gpu(term, Name("kernel"), [Name("input")], [GInt])
    assert "TODO" in ir


def test_logical_not():
    term = Let(Name("x"), Application(Var(Name("!")), Literal(True, t_bool)), Var(Name("x")))
    ir = compile_to_gpu(term, Name("kernel"), [Name("input")], [GBool])
    assert "TODO" in ir


def test_if_expression():
    cond = Application(Application(Var(Name(">")), Var(Name("input"))), Literal(0, t_int))
    term = If(cond, Literal(1, t_int), Literal(0, t_int))
    ir = compile_to_gpu(term, Name("kernel"), [Name("input")], [GInt])
    assert "TODO" in ir


def test_multiple_binops():
    term = Application(
        Application(Var(Name("+")), Application(Application(Var(Name("*")), Var(Name("input"))), Literal(2, t_int))),
        Literal(1, t_int),
    )
    ir = compile_to_gpu(term, Name("kernel"), [Name("input")], [GInt])
    assert "TODO" in ir


def test_unsupported_type_error():
    t_string = TypeConstructor(Name("String", 0), [])
    term = Literal("hello", t_string)
    with pytest.raises(Exception, match="GPU Kernels do not support type: String"):
        compile_to_gpu(term, Name("kernel"), [], [])


def test_unsupported_op_error():
    term = Application(Var(Name("print")), Literal(1, t_int))
    with pytest.raises(Exception, match="GPU Kernels do not support operation print"):
        compile_to_gpu(term, Name("kernel"), [], [])


def test_recursion_error():
    f_name = Name("f")
    body = Application(Var(f_name), Var(Name("x")))
    term = Rec(f_name, t_int, body, Var(Name("x")))
    with pytest.raises(
        Exception, match="GPU Kernels do not support operation f"
    ):  # technically in the future will be a recursion error, for now it's like this
        compile_to_gpu(term, f_name, [Name("x")], [GInt])


def test_float_ops():
    term = Application(Application(Var(Name("+")), Literal(1.5, t_float)), Literal(2.5, t_float))
    ir = compile_to_gpu(term, Name("kernel"), [], [])
    assert "TODO" in ir


def test_comparison_ops():
    term = Application(Application(Var(Name("<=")), Var(Name("input"))), Literal(10, t_int))
    ir = compile_to_gpu(term, Name("kernel"), [Name("input")], [GInt])
    assert "TODO" in ir
