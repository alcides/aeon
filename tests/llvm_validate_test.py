import pytest

from aeon.core.terms import Literal, Application, Var, Let, Abstraction
from aeon.core.types import TypeConstructor
from aeon.llvm.core import LLVMValidationError
from aeon.llvm.cpu.lowerer import CPULLVMLowerer, CPUValidationContext
from aeon.utils.name import Name


def test_validate_valid_cpu():
    # let f = \x -> \y -> x + y in f
    body = Application(Application(Var(Name("+")), Var(Name("x"))), Var(Name("y")))
    func = Abstraction(Name("x"), Abstraction(Name("y"), body))
    term = Let(Name("f"), func, Var(Name("f")))

    lowerer = CPULLVMLowerer()
    ctx = CPUValidationContext(allowed_func_calls={Name("f"), Name("+")})
    lowerer.validate(term, ctx)


def test_validate_invalid_type():
    # 'String is not supported'
    t_string = TypeConstructor(Name("String"))
    term = Literal("hello", t_string)

    lowerer = CPULLVMLowerer()
    with pytest.raises(LLVMValidationError):
        lowerer.validate(term, CPUValidationContext())


def test_validate_invalid_call_non_llvm():
    # let f = \x -> external_func x in f
    body = Application(Var(Name("external_func")), Var(Name("x")))
    func = Abstraction(Name("x"), body)
    term = Let(Name("f"), func, Var(Name("f")))

    lowerer = CPULLVMLowerer()
    with pytest.raises(LLVMValidationError):
        # 'f' is allowed, but 'external_func' (used in body) is not
        ctx = CPUValidationContext(allowed_func_calls={Name("f")})
        lowerer.validate(term, ctx)


# def test_validate_partial_application():
#     # let f = \x -> \y -> x + y in f 1
#     t_int = TypeConstructor(Name("Int"))
#     t_f = AbstractionType(Name("x"), t_int, AbstractionType(Name("y"), t_int, t_int))
#
#     f_def = Annotation(
#         Abstraction(
#             Name("x"), Abstraction(Name("y"), Application(Application(Var(Name("+")), Var(Name("x"))), Var(Name("y"))))
#         ),
#         t_f,
#     )
#
#     call = Application(Var(Name("f")), Literal(1, t_int))  # f 1
#     term = Let(Name("f"), f_def, call)
#
#     lowerer = CPULLVMLowerer()
#     with pytest.raises(LLVMValidationError):
#         ctx = CPUValidationContext(allowed_func_calls={Name("f"), Name("+")})
#         lowerer.validate(term, ctx)
