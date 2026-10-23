"""Split array expressions into ordinary compiled stages and fuse elementwise lambdas.

This pass runs after lowering. CPU and CUDA execute the same plan; each stage still
uses the normal LLVM expression visitor, including callbacks and scalar helpers.
"""

from __future__ import annotations

from dataclasses import dataclass, fields, replace
from typing import Any

from aeon.bindings.ndarray import NDArray, ManagedArray
from aeon.llvm.core import LLVMBackendError
from aeon.llvm.llvm_ast import (
    LLVMTerm,
    LLVMVar,
    LLVMLiteral,
    LLVMLet,
    LLVMFunction,
    LLVMFunctionType,
    LLVMNDArrayOp,
    LLVMNDArrayType,
    LLVMVectorReduce,
    LLVMVectorFilter,
    LLVMRefinedValue,
    LLVMCall,
    LLVMIf,
    LLVMCast,
)
from aeon.llvm.utils import sanitize_name
from aeon.utils.name import Name

ARRAY_OPS = {"map", "zipWith", "scan", "scan_exclusive", "reduce_axis"}


def children(term):
    for member in fields(term):
        value = getattr(term, member.name)
        if isinstance(value, LLVMTerm):
            yield value
        elif isinstance(value, list):
            yield from (child for child in value if isinstance(child, LLVMTerm))


def transform(term, visit):
    changes = {}
    for member in fields(term):
        value = getattr(term, member.name)
        if isinstance(value, LLVMTerm):
            changes[member.name] = visit(value)
        elif isinstance(value, list):
            changes[member.name] = [visit(child) if isinstance(child, LLVMTerm) else child for child in value]
    return replace(term, **changes)


def substitute(term, bindings):
    if isinstance(term, LLVMVar):
        return bindings.get(term.name, term)
    if isinstance(term, LLVMFunction):
        return replace(term, body=substitute(term.body, {k: v for k, v in bindings.items() if k not in term.arg_names}))
    if isinstance(term, LLVMLet):
        return replace(
            term,
            var_value=substitute(term.var_value, bindings),
            body=substitute(term.body, {k: v for k, v in bindings.items() if k != term.var_name}),
        )
    return transform(term, lambda child: substitute(child, bindings))


def variables(term, bound=frozenset()):
    result = {}
    if isinstance(term, LLVMVar) and term.name not in bound:
        result[term.name] = term.type
    elif isinstance(term, LLVMFunction):
        result.update(variables(term.body, bound | set(term.arg_names)))
    elif isinstance(term, LLVMLet):
        result.update(variables(term.var_value, bound))
        result.update(variables(term.body, bound | {term.var_name}))
    else:
        for child in children(term):
            result.update(variables(child, bound))
    return result


def occurrences(term, name):
    return int(isinstance(term, LLVMVar) and term.name == name) + sum(
        occurrences(child, name) for child in children(term)
    )


def collective(term):
    return isinstance(term, (LLVMVectorReduce, LLVMVectorFilter)) or (
        isinstance(term, LLVMNDArrayOp) and term.op in ARRAY_OPS | {"fill", "map_rows"}
    )


def has_collective(term):
    if isinstance(term, LLVMFunction):
        return False
    return collective(term) or any(has_collective(child) for child in children(term))


def normalize(term, definitions, stack=()):
    if isinstance(term, LLVMRefinedValue):
        # Stage boundaries are retyped. Do not carry facts about eliminated locals.
        return normalize(term.value, definitions, stack)
    if isinstance(term, LLVMLet):
        value = normalize(term.var_value, definitions, stack)
        # Linear array values have one consumer; scalar bindings remain shared.
        if (
            isinstance(value, LLVMFunction)
            or isinstance(value.type, LLVMNDArrayType)
            and occurrences(term.body, term.var_name) == 1
        ):
            return normalize(substitute(term.body, {term.var_name: value}), definitions, stack)
        return replace(term, var_value=value, body=normalize(term.body, definitions, stack))
    if isinstance(term, LLVMCall):
        target = term.target
        callee = (
            target
            if isinstance(target, LLVMFunction)
            else definitions.get(target.name)
            if isinstance(target, LLVMVar)
            else None
        )
        if callee is not None and has_collective(callee.body):
            if callee.name in stack:
                raise LLVMBackendError("Recursive array pipelines need a host loop around the GPU entry")
            return normalize(
                substitute(callee.body, dict(zip(callee.arg_names, term.args))), definitions, stack + (callee.name,)
            )
    if isinstance(term, LLVMFunction):
        return term
    term = transform(term, lambda child: normalize(child, definitions, stack))
    if isinstance(term, LLVMNDArrayOp) and term.op == "map":
        inner = term.array
        if isinstance(inner, LLVMNDArrayOp) and inner.op in {"map", "zipWith"}:
            first, second = inner.args[-1], term.args[0]
            if isinstance(first, LLVMFunction) and isinstance(second, LLVMFunction):
                intermediate = Name("fused_value")
                body = LLVMLet(
                    second.body.type,
                    intermediate,
                    LLVMCast(first.type.return_type, first.body),
                    substitute(second.body, {second.arg_names[0]: LLVMVar(first.type.return_type, intermediate)}),
                )
                callback = replace(first, type=LLVMFunctionType(first.arg_types, second.type.return_type), body=body)
                return replace(inner, type=term.type, args=[*inner.args[:-1], callback])
    return term


@dataclass
class Stage:
    function: LLVMFunction
    arguments: list[Name]
    result: Name
    operation: LLVMNDArrayOp | None = None


@dataclass
class Branch:
    condition: LLVMTerm
    yes: list[Any]
    no: list[Any]
    yes_result: LLVMTerm
    no_result: LLVMTerm
    result: Name


@dataclass
class ArrayPlan:
    parameters: list[Name]
    steps: list[Any]
    result: LLVMTerm

    def run(self, arguments, invoke):
        values = dict(zip(self.parameters, arguments))

        def resolve(term):
            return term.value if isinstance(term, LLVMLiteral) else values[term.name]

        def run_steps(steps):
            for step in steps:
                if isinstance(step, Branch):
                    yes = resolve(step.condition)
                    run_steps(step.yes if yes else step.no)
                    values[step.result] = resolve(step.yes_result if yes else step.no_result)
                    continue
                args = [values[name] for name in step.arguments]
                if step.operation is not None:
                    op = step.operation
                    source = resolve(op.array)
                    if not isinstance(source, NDArray):
                        raise ValueError("Array pipelines require NDArray inputs")
                    shape = source.shape
                    if op.op == "zipWith" and resolve(op.args[0]).shape != shape:
                        raise ValueError("zipWith requires identical shapes")
                    if op.op == "reduce_axis":
                        axis = resolve(op.args[0])
                        source.dimension(axis)  # Validate before allocating or launching.
                        shape = shape[:axis] + (1,) + shape[axis + 1 :]
                    reuse = op.type == op.array.type and shape == source.shape and op.op != "reduce_axis"
                    if reuse:
                        destination = source
                    else:
                        import math

                        destination = NDArray(ManagedArray([0] * math.prod(shape)), shape)
                    args.append(destination)
                    values[step.result] = invoke(step.function, args, step.operation, destination)
                else:
                    values[step.result] = invoke(step.function, args, None, None)

        run_steps(self.steps)
        return resolve(self.result)


def build_plans(definitions):
    functions = {node.name: node for node in definitions if isinstance(node, LLVMFunction)}
    generated, plans = [], {}
    for node in definitions:
        if not isinstance(node, LLVMFunction):
            generated.append(node)
            continue
        body = normalize(node.body, functions)
        # Preserve the established direct-entry ABI for existing operations.
        needs_plan = has_collective(body) and (
            not collective(body)
            or any(has_collective(c) for c in children(body))
            or isinstance(body, LLVMNDArrayOp)
            and body.op in ARRAY_OPS
        )
        if not needs_plan:
            generated.append(node)
            continue
        scope = dict(zip(node.arg_names, node.arg_types))
        steps = []
        counter = 0

        def fresh(label):
            nonlocal counter
            counter += 1
            return Name(f"{sanitize_name(node.name)}__{label}_{counter}")

        def stage(expression, target_steps, operation=None):
            used = variables(expression)
            names = [name for name in used if name in scope]
            types = [scope[name] for name in names]
            if operation is not None:
                destination = fresh("output")
                types.append(operation.type)
                expression = LLVMNDArrayOp(
                    operation.type,
                    operation.op + "_into",
                    LLVMVar(operation.type, destination),
                    [operation.array, *operation.args],
                )
            result, name = fresh("value"), fresh("stage")
            fn = LLVMFunction(
                LLVMFunctionType(types, expression.type),
                names + ([destination] if operation is not None else []),
                types,
                expression,
                name=name,
            )
            generated.append(fn)
            target_steps.append(Stage(fn, names, result, operation))
            scope[result] = expression.type
            return LLVMVar(expression.type, result)

        def lower(term, target_steps):
            if isinstance(term, (LLVMVar, LLVMLiteral)):
                return term
            if isinstance(term, LLVMFunction):
                return term
            if isinstance(term, LLVMLet):
                value = lower(term.var_value, target_steps)
                return lower(substitute(term.body, {term.var_name: value}), target_steps)
            if isinstance(term, LLVMIf) and has_collective(term):
                condition = lower(term.cond, target_steps)
                yes_steps, no_steps = [], []
                yes, no = lower(term.then_t, yes_steps), lower(term.else_t, no_steps)
                result = fresh("branch")
                scope[result] = term.type
                target_steps.append(Branch(condition, yes_steps, no_steps, yes, no, result))
                return LLVMVar(term.type, result)
            if isinstance(term, (LLVMVectorReduce, LLVMVectorFilter)):
                source = lower(term.v, target_steps)
                from aeon.llvm.llvm_ast import LLVMInt

                size = (
                    LLVMNDArrayOp(LLVMInt, "elements", source, [])
                    if isinstance(source.type, LLVMNDArrayType)
                    else lower(term.size, target_steps)
                )
                changes = {"v": source, "size": size}
                if isinstance(term, LLVMVectorReduce):
                    changes["initial"] = lower(term.initial, target_steps)
                return stage(replace(term, **changes), target_steps)
            if isinstance(term, LLVMNDArrayOp):
                source = lower(term.array, target_steps)
                args = [lower(arg, target_steps) for arg in term.args]
                operation = replace(term, array=source, args=args)
                return stage(operation, target_steps, operation if term.op in ARRAY_OPS else None)
            if has_collective(term):
                term = transform(term, lambda child: lower(child, target_steps))
            return stage(term, target_steps)

        result = lower(body, steps)
        plans[node.name] = ArrayPlan(node.arg_names, steps, result)
    return generated, plans
