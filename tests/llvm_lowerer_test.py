from aeon.core.terms import Literal, Application, Var, Abstraction
from aeon.core.types import t_int
from aeon.llvm.cpu.lowerer import CPULLVMLowerer
from aeon.llvm.llvm_ast import LLVMFunctionType, LLVMInt, LLVMCall, LLVMFunction, LLVMLiteral
from aeon.utils.name import Name


def test_lower_literal():
    lowerer = CPULLVMLowerer()
    lit = Literal(42, t_int)
    llvm_lit = lowerer.lower(lit)
    assert isinstance(llvm_lit, LLVMLiteral)
    assert llvm_lit.value == 42
    assert llvm_lit.type == LLVMInt


def test_lower_var_op():
    lowerer = CPULLVMLowerer()
    var_plus = Var(Name("+"))
    llvm_plus = lowerer.lower(var_plus)

    assert isinstance(llvm_plus.type, LLVMFunctionType)
    assert llvm_plus.type.arg_types == [LLVMInt, LLVMInt]
    assert llvm_plus.type.return_type == LLVMInt


def test_lower_full_application():
    lowerer = CPULLVMLowerer()
    plus = Var(Name("+"))
    app = Application(Application(plus, Var(Name("x"))), Var(Name("y")))

    type_env = {Name("x"): LLVMInt, Name("y"): LLVMInt}
    llvm_call = lowerer.lower(app, type_env=type_env)

    assert isinstance(llvm_call, LLVMCall)
    assert len(llvm_call.args) == 2
    assert llvm_call.type == LLVMInt


def test_lower_abstraction_full():
    lowerer = CPULLVMLowerer()
    body = Application(Application(Var(Name("+")), Var(Name("x"))), Var(Name("y")))
    func = Abstraction(Name("x"), Abstraction(Name("y"), body))

    expected_type = LLVMFunctionType([LLVMInt, LLVMInt], LLVMInt)
    llvm_abs = lowerer.lower(func, expected_type=expected_type)

    assert isinstance(llvm_abs, LLVMFunction)
    assert llvm_abs.arg_names == [Name("x"), Name("y")]
    assert llvm_abs.arg_types == [LLVMInt, LLVMInt]
    assert llvm_abs.type == expected_type
