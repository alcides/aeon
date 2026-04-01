import pytest

from aeon.llvm.cpu.converter import CPULLVMIRGenerator, LLVMIRGenerationError
from aeon.llvm.llvm_ast import (
    LLVMInt,
    LLVMBool,
    LLVMLiteral,
    LLVMVar,
    LLVMIf,
    LLVMLet,
    LLVMAbstraction,
    LLVMCall,
    LLVMFunctionType,
)
from aeon.utils.name import Name


def test_generate_literal():
    generator = CPULLVMIRGenerator()

    func_type = LLVMFunctionType(arg_types=[], return_type=LLVMInt)
    func_ast = LLVMAbstraction(type=func_type, arg_names=[], arg_types=[], body=LLVMLiteral(type=LLVMInt, value=42))

    kernel_ast = LLVMLet(
        type=LLVMInt, var_name=Name("my_const"), var_value=func_ast, body=LLVMLiteral(type=LLVMInt, value=0)
    )

    ir_code = generator.generate_kernels([kernel_ast])
    print(ir_code)

    assert 'define i32 @"my_const' in ir_code
    assert "ret i32 42" in ir_code


def test_generate_if_else():
    generator = CPULLVMIRGenerator()

    cond = LLVMLiteral(type=LLVMBool, value=True)
    then_t = LLVMLiteral(type=LLVMInt, value=10)
    else_t = LLVMLiteral(type=LLVMInt, value=20)
    if_ast = LLVMIf(type=LLVMInt, cond=cond, then_t=then_t, else_t=else_t)

    func_type = LLVMFunctionType(arg_types=[], return_type=LLVMInt)
    func_ast = LLVMAbstraction(type=func_type, arg_names=[], arg_types=[], body=if_ast)
    kernel_ast = LLVMLet(
        type=LLVMInt, var_name=Name("my_branch"), var_value=func_ast, body=LLVMLiteral(type=LLVMInt, value=0)
    )

    ir_code = generator.generate_kernels([kernel_ast])
    print(ir_code)

    assert 'define i32 @"my_branch' in ir_code
    assert "br i1 1" in ir_code
    assert "phi  i32" in ir_code
    assert "[10," in ir_code
    assert "[20," in ir_code


def test_generate_local_let_shadowing():
    generator = CPULLVMIRGenerator()

    inner_let = LLVMLet(
        type=LLVMInt,
        var_name=Name("x"),
        var_value=LLVMLiteral(type=LLVMInt, value=10),
        body=LLVMVar(type=LLVMInt, name=Name("x")),
    )
    outer_let = LLVMLet(type=LLVMInt, var_name=Name("x"), var_value=LLVMLiteral(type=LLVMInt, value=5), body=inner_let)

    func_type = LLVMFunctionType(arg_types=[], return_type=LLVMInt)
    func_ast = LLVMAbstraction(type=func_type, arg_names=[], arg_types=[], body=outer_let)
    kernel_ast = LLVMLet(
        type=LLVMInt, var_name=Name("my_shadow"), var_value=func_ast, body=LLVMLiteral(type=LLVMInt, value=0)
    )

    ir_code = generator.generate_kernels([kernel_ast])
    print(ir_code)
    assert "ret i32 10" in ir_code


def test_generate_abstraction_and_call():
    generator = CPULLVMIRGenerator()

    func_type = LLVMFunctionType(arg_types=[LLVMInt, LLVMInt], return_type=LLVMInt)
    func_ast = LLVMAbstraction(
        type=func_type,
        arg_names=[Name("x"), Name("y")],
        arg_types=[LLVMInt, LLVMInt],
        body=LLVMVar(type=LLVMInt, name=Name("x")),
    )

    caller_type = LLVMFunctionType(arg_types=[], return_type=LLVMInt)
    call_ast = LLVMCall(
        type=LLVMInt,
        target=LLVMVar(type=func_type, name=Name("my_func")),
        args=[LLVMLiteral(type=LLVMInt, value=42), LLVMLiteral(type=LLVMInt, value=10)],
    )
    caller_ast = LLVMAbstraction(type=caller_type, arg_names=[], arg_types=[], body=call_ast)

    program_ast = LLVMLet(
        type=LLVMInt,
        var_name=Name("my_func"),
        var_value=func_ast,
        body=LLVMLet(
            type=LLVMInt, var_name=Name("my_caller"), var_value=caller_ast, body=LLVMLiteral(type=LLVMInt, value=0)
        ),
    )

    ir_code = generator.generate_kernels([program_ast])
    print(ir_code)

    assert 'define i32 @"my_func"(i32 %"x", i32 %"y")' in ir_code
    assert 'define i32 @"my_caller' in ir_code
    assert 'call i32 @"my_func"(i32 42, i32 10)' in ir_code


def test_generate_sum_with_if():
    generator = CPULLVMIRGenerator()

    sum_type = LLVMFunctionType(arg_types=[LLVMInt, LLVMInt], return_type=LLVMInt)
    sum_func = LLVMAbstraction(
        type=sum_type,
        arg_names=[Name("x"), Name("y")],
        arg_types=[LLVMInt, LLVMInt],
        body=LLVMCall(
            type=LLVMInt,
            target=LLVMVar(type=sum_type, name=Name("+")),
            args=[LLVMVar(type=LLVMInt, name=Name("x")), LLVMVar(type=LLVMInt, name=Name("y"))],
        ),
    )

    main_type = LLVMFunctionType(arg_types=[], return_type=LLVMInt)

    x_var = LLVMVar(type=LLVMInt, name=Name("x"))
    cond = LLVMCall(
        type=LLVMBool,
        target=LLVMVar(type=LLVMFunctionType([LLVMInt, LLVMInt], LLVMBool), name=Name("<")),
        args=[x_var, LLVMLiteral(type=LLVMInt, value=3)],
    )
    y_val = LLVMIf(
        type=LLVMInt,
        cond=cond,
        then_t=LLVMLiteral(type=LLVMInt, value=7),
        else_t=LLVMLiteral(type=LLVMInt, value=10),
    )

    body = LLVMLet(
        type=LLVMInt,
        var_name=Name("x"),
        var_value=LLVMLiteral(type=LLVMInt, value=5),
        body=LLVMLet(
            type=LLVMInt,
            var_name=Name("y"),
            var_value=y_val,
            body=LLVMCall(
                type=LLVMInt,
                target=LLVMVar(type=sum_type, name=Name("sum")),
                args=[LLVMVar(type=LLVMInt, name=Name("x")), LLVMVar(type=LLVMInt, name=Name("y"))],
            ),
        ),
    )

    main_func = LLVMAbstraction(type=main_type, arg_names=[], arg_types=[], body=body)

    program_ast = LLVMLet(
        type=LLVMInt,
        var_name=Name("sum"),
        var_value=sum_func,
        body=LLVMLet(
            type=LLVMInt,
            var_name=Name("main"),
            var_value=main_func,
            body=LLVMLiteral(type=LLVMInt, value=0),
        ),
    )

    ir_code = generator.generate_kernels([program_ast])
    print(ir_code)

    assert 'define i32 @"sum' in ir_code
    assert 'define i32 @"main' in ir_code
    assert "add i32" in ir_code
    assert "icmp slt i32" in ir_code


def test_generate_unary_op():
    generator = CPULLVMIRGenerator()

    func_type = LLVMFunctionType(arg_types=[LLVMInt], return_type=LLVMInt)
    func_ast = LLVMAbstraction(
        type=func_type,
        arg_names=[Name("x")],
        arg_types=[LLVMInt],
        body=LLVMCall(
            type=LLVMInt,
            target=LLVMVar(type=LLVMFunctionType([LLVMInt], LLVMInt), name=Name("-")),
            args=[LLVMVar(type=LLVMInt, name=Name("x"))],
        ),
    )

    kernel_ast = LLVMLet(
        type=LLVMInt,
        var_name=Name("my_neg"),
        var_value=func_ast,
        body=LLVMLiteral(type=LLVMInt, value=0),
    )

    ir_code = generator.generate_kernels([kernel_ast])
    print(ir_code)

    assert 'define i32 @"my_neg' in ir_code
    assert "sub i32 0," in ir_code


def test_undefined_variable_raises_error():
    generator = CPULLVMIRGenerator()

    bad_var = LLVMVar(type=LLVMInt, name=Name("not_found"))

    func_type = LLVMFunctionType(arg_types=[], return_type=LLVMInt)
    func_ast = LLVMAbstraction(type=func_type, arg_names=[], arg_types=[], body=bad_var)
    kernel_ast = LLVMLet(
        type=LLVMInt, var_name=Name("bad_kernel"), var_value=func_ast, body=LLVMLiteral(type=LLVMInt, value=0)
    )

    with pytest.raises(LLVMIRGenerationError):
        generator.generate_kernels([kernel_ast])
