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


def test_lower_vector_get():
    lowerer = CPULLVMLowerer()
    # get vec 0
    app = Application(Application(Var(Name("get")), Var(Name("vec"))), Literal(0, t_int))
    from aeon.llvm.llvm_ast import LLVMPointerType

    type_env = {Name("vec"): LLVMPointerType(LLVMInt)}
    llvm_get = lowerer.lower(app, type_env=type_env)
    assert llvm_get.type == LLVMInt


def test_lower_vector_map():
    lowerer = CPULLVMLowerer()
    # map (\x -> x + 1) vec sz
    kernel = Abstraction(Name("x"), Application(Application(Var(Name("+")), Var(Name("x"))), Literal(1, t_int)))
    app = Application(Application(Application(Var(Name("map")), kernel), Var(Name("vec"))), Var(Name("sz")))
    from aeon.llvm.llvm_ast import LLVMPointerType

    type_env = {Name("vec"): LLVMPointerType(LLVMInt), Name("sz"): LLVMInt}
    llvm_map = lowerer.lower(app, type_env=type_env)
    assert isinstance(llvm_map.type, LLVMPointerType)
    assert llvm_map.type.element_type == LLVMInt


def test_lower_math_pow():
    lowerer = CPULLVMLowerer()
    # pow is (Int, Int) -> Int; mixed float literal is cast to Int.
    app = Application(Application(Var(Name("pow")), Literal(2, t_int)), Literal(3, t_int))
    llvm_pow = lowerer.lower(app)
    from aeon.llvm.llvm_ast import LLVMInt

    assert llvm_pow.type == LLVMInt

    # Float exponentiation uses powf : (Double, Double) -> Double
    from aeon.core.types import t_float
    from aeon.llvm.llvm_ast import LLVMDouble

    appf = Application(Application(Var(Name("powf")), Literal(2.0, t_float)), Literal(3.0, t_float))
    llvm_powf = lowerer.lower(appf)
    assert llvm_powf.type == LLVMDouble
