import pytest
from aeon.core.terms import Literal, Application, Var, Let, Abstraction
from aeon.core.types import TypeConstructor
from aeon.llvm.cpu.lowerer import CPULLVMLowerer
from aeon.llvm.core import LLVMValidationError
from aeon.utils.name import Name


def test_validate_valid_cpu():
    # let f = \x -> \y -> x + y in f
    body = Application(Application(Var(Name("+")), Var(Name("x"))), Var(Name("y")))
    func = Abstraction(Name("x"), Abstraction(Name("y"), body))
    term = Let(Name("f"), func, Var(Name("f")))

    lowerer = CPULLVMLowerer()
    lowerer.validate(term, allowed_func_calls={Name("f")})


def test_validate_invalid_type():
    # 'String is not supported'
    t_string = TypeConstructor(Name("String"))
    term = Literal("hello", t_string)

    lowerer = CPULLVMLowerer()
    with pytest.raises(LLVMValidationError):
        lowerer.validate(term)


def test_validate_invalid_call_non_llvm():
    # let f = \x -> external_func x in f
    body = Application(Var(Name("external_func")), Var(Name("x")))
    func = Abstraction(Name("x"), body)
    term = Let(Name("f"), func, Var(Name("f")))

    lowerer = CPULLVMLowerer()
    with pytest.raises(LLVMValidationError):
        # 'f' is allowed, but 'external_func' (used in body) is not
        lowerer.validate(term, allowed_func_calls={Name("f")})


def test_validate_declared_but_not_allowed():
    # let external_func = \x -> x in
    # let f = \x -> external_func x in
    # f
    external_func_def = Abstraction(Name("x"), Var(Name("x")))

    f_body = Application(Var(Name("external_func")), Var(Name("x")))
    f_def = Abstraction(Name("x"), f_body)

    term = Let(Name("external_func"), external_func_def, Let(Name("f"), f_def, Var(Name("f"))))

    lowerer = CPULLVMLowerer()

    with pytest.raises(LLVMValidationError):
        lowerer.validate(term, allowed_func_calls={Name("f")})

    lowerer.validate(term, allowed_func_calls={Name("f"), Name("external_func")})
