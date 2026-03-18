import pytest

from aeon.core.terms import Literal, Application, Var, Let, Abstraction, Annotation
from aeon.core.types import TypeConstructor, AbstractionType
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
    t_unsupported = TypeConstructor(Name("UnsupportedType"))
    term = Literal(1, t_unsupported)

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
        ctx = CPUValidationContext(allowed_func_calls={Name("f")}, strict=True)
        lowerer.validate(term, ctx)
