from aeon.facade.driver import AeonDriver, AeonConfig
from aeon.llvm.cpu.converter import CPULLVMIRGenerator
from aeon.llvm.cpu.lowerer import CPULLVMLowerer
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SynthesisUI


def test_e2e_sum_floats_to_llvm():
    source = """
    def special_sum (x:Float) (y:Float) : Float {
        let w = 5.0;
        let z = 10.0;
        x + y - z * w
    }

    def main (i:Int) : Float {
        special_sum 5.0 7.0
    }
    """
    setup_logger()

    cfg = AeonConfig(synthesizer="random", synthesis_ui=SynthesisUI(), synthesis_budget=0, no_main=False)
    driver = AeonDriver(cfg)

    errors = driver.parse(aeon_code=source)
    assert not errors

    core_ast = driver.core
    print(f"\n[core ast]:\n{core_ast}")

    lowerer = CPULLVMLowerer()
    llvm_ast = lowerer.lower(core_ast)

    generator = CPULLVMIRGenerator()
    llvm_ir = generator.generate_kernels([llvm_ast])

    print(f"\n[llvm ir]:\n{llvm_ir}")

    assert 'define float @"special_sum' in llvm_ir
    assert 'define float @"main' in llvm_ir


def test_e2e_recursive_to_llvm():
    source = """
def count_divisors (target:Int) (candidate:Int) : Int {
    if candidate <= 0 then
        0
    else
        let remainder = target % candidate;
        if remainder == 0 then
            1 + count_divisors target (candidate - 1)
        else
            count_divisors target (candidate - 1)
}

def main (i:Int) : Int {
    count_divisors 100 50
}
    """

    setup_logger()

    cfg = AeonConfig(synthesizer="random", synthesis_ui=SynthesisUI(), synthesis_budget=0, no_main=False)
    driver = AeonDriver(cfg)

    errors = driver.parse(aeon_code=source)
    assert not errors

    core_ast = driver.core
    print(f"\n[core ast]\n{core_ast}")

    lowerer = CPULLVMLowerer()
    llvm_ast = lowerer.lower(core_ast)

    generator = CPULLVMIRGenerator()
    llvm_ir = generator.generate_kernels([llvm_ast])

    print(f"\n[llvm ir]\n{llvm_ir}")
    assert 'define i32 @"count_divisors' in llvm_ir
    assert 'define i32 @"main' in llvm_ir
