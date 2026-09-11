"""Guard refinement hints against the mathematical-Int / machine-Int gap.

An Aeon proof uses unbounded integers. A wrapped intermediate can change a
branch and invalidate an otherwise proved refinement. Disable hints for the
whole compilation unit unless simple interval analysis rules that out. The
checked function contracts supply the inductive hypotheses for recursive calls.
This is conservative: unsupported operations lose hints, not executability.
"""

from dataclasses import fields

from aeon.llvm.llvm_ast import (
    LLVMCall,
    LLVMCast,
    LLVMFunction,
    LLVMFunctionType,
    LLVMIf,
    LLVMIntType,
    LLVMLet,
    LLVMLiteral,
    LLVMRefinedValue,
    LLVMTerm,
    LLVMVar,
)
from aeon.llvm.refinements import integer_range, result_refinement


def full_range(ty):
    if isinstance(ty, LLVMIntType):
        return -(1 << (ty.bits - 1)), (1 << (ty.bits - 1)) - 1
    return None


def refinement_arithmetic_is_safe(definitions: list[LLVMTerm]) -> bool:
    safe = True

    def bounded(ty, values):
        nonlocal safe
        limits = full_range(ty)
        if limits is None or values is None:
            return limits
        if values[0] < limits[0] or values[1] > limits[1]:
            safe = False
            return limits
        return values

    def visit(node, env):
        nonlocal safe
        limits = full_range(node.type)
        if isinstance(node, LLVMLiteral):
            return bounded(node.type, (int(node.value), int(node.value))) if limits else None
        if isinstance(node, LLVMVar):
            return env.get(node.name, limits)
        if isinstance(node, LLVMFunction):
            local = dict(env)
            for arg, ty in zip(node.arg_names, node.arg_types):
                bounds = full_range(ty)
                if bounds:
                    for fact in node.refinements:
                        interval = integer_range(fact, arg, ty.bits)
                        if interval:
                            bounds = max(bounds[0], interval[0]), min(bounds[1], interval[1] - 1)
                local[arg] = bounds
            visit(node.body, local)
            return None
        if isinstance(node, LLVMLet):
            value = visit(node.var_value, env)
            return visit(node.body, {**env, node.var_name: value})
        if isinstance(node, LLVMRefinedValue):
            value = visit(node.value, env)
            if limits:
                ref = node.refinement
                interval = integer_range(ref.refinement, ref.name, node.type.bits)
                if interval:
                    return max(value[0], interval[0]), min(value[1], interval[1] - 1)
            return value
        if isinstance(node, LLVMIf):
            visit(node.cond, env)
            left, right = visit(node.then_t, env), visit(node.else_t, env)
            return (min(left[0], right[0]), max(left[1], right[1])) if left and right else limits
        if isinstance(node, LLVMCast):
            value = visit(node.val, env)
            if limits and value is None:
                safe = False  # Floating-point to integer conversion needs a separate proof.
            return bounded(node.type, value)
        if isinstance(node, LLVMCall):
            args = [visit(arg, env) for arg in node.args]
            op = node.target.name.name if isinstance(node.target, LLVMVar) else None
            if limits and op in {"+", "-", "*", "/", "%"}:
                if any(a is None for a in args):
                    safe = False
                    return limits
                a = args[0]
                if len(args) == 1 and op == "-":
                    return bounded(node.type, (-a[1], -a[0]))
                if len(args) != 2:
                    safe = False
                    return limits
                b = args[1]
                if op == "+":
                    return bounded(node.type, (a[0] + b[0], a[1] + b[1]))
                if op == "-":
                    return bounded(node.type, (a[0] - b[1], a[1] - b[0]))
                if op == "*":
                    products = [x * y for x in a for y in b]
                    return bounded(node.type, (min(products), max(products)))
                if b[0] <= 0 <= b[1] or (a[0] <= limits[0] <= a[1] and b[0] <= -1 <= b[1]):
                    safe = False
                return limits
            if limits and isinstance(node.target.type, LLVMFunctionType):
                ref = result_refinement(node.target.type.source_type)
                interval = integer_range(ref.refinement, ref.name, node.type.bits) if ref else None
                if interval:
                    return interval[0], interval[1] - 1
            return limits
        # Memory and vector nodes may contain arithmetic in their children.
        for field in fields(node):
            value = getattr(node, field.name)
            if isinstance(value, LLVMTerm):
                visit(value, env)
            elif isinstance(value, list):
                for item in value:
                    if isinstance(item, LLVMTerm):
                        visit(item, env)
        return limits

    for definition in definitions:
        visit(definition, {})
    return safe
