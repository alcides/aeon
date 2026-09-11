"""Conservative lowering of checked integer refinements to LLVM facts.

Aeon's predicates use mathematical integers. Only direct comparisons of
representable integer values are lowered: arithmetic, floating point, calls,
and unknown predicates are deliberately omitted, never guessed.
"""

from __future__ import annotations

from collections.abc import Mapping

import llvmlite.ir as ir

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidTerm, LiquidVar
from aeon.core.types import AbstractionType, RefinedType, Type
from aeon.utils.name import Name


def rename_predicate(t: LiquidTerm, names: Mapping[Name, Name]) -> LiquidTerm:
    if isinstance(t, LiquidVar):
        return LiquidVar(names.get(t.name, t.name))
    if isinstance(t, LiquidApp):
        return LiquidApp(t.fun, [rename_predicate(a, names) for a in t.args])
    return t


def parameter_facts(ty: Type | None, args: list[Name]) -> list[LiquidTerm]:
    facts = []
    names: dict[Name, Name] = {}
    for arg in args:
        if not isinstance(ty, AbstractionType):
            break
        if isinstance(ty.var_type, RefinedType):
            ref = ty.var_type
            facts.append(rename_predicate(ref.refinement, {**names, ref.name: arg}))
        names[ty.var_name] = arg
        ty = ty.type
    return facts


def result_refinement(ty: Type | None) -> RefinedType | None:
    while isinstance(ty, AbstractionType):
        ty = ty.type
    return ty if isinstance(ty, RefinedType) else None


def integer_range(predicate: LiquidTerm, binder: Name, bits: int) -> tuple[int, int] | None:
    """Return a nonempty signed interval [lo, hi), or None when uninformative.

    LLVM endpoints are bit patterns; callers encode the exclusive upper bound
    modulo 2**bits (including the signed maximum + 1).
    """
    minimum, maximum = -(1 << (bits - 1)), 1 << (bits - 1)
    lo, hi = minimum, maximum
    atoms = [predicate]
    while atoms:
        atom = atoms.pop()
        if isinstance(atom, LiquidApp) and atom.fun.name == "&&":
            atoms.extend(atom.args)
            continue
        if not isinstance(atom, LiquidApp) or len(atom.args) != 2:
            continue
        left, right = atom.args
        op = atom.fun.name
        if isinstance(right, LiquidVar) and right.name == binder and isinstance(left, LiquidLiteralInt):
            left, right = right, left
            op = {"<": ">", "<=": ">=", ">": "<", ">=": "<=", "==": "=="}.get(op, "")
        if not (isinstance(left, LiquidVar) and left.name == binder and isinstance(right, LiquidLiteralInt)):
            continue
        n = right.value
        if not minimum <= n < maximum:
            continue
        if op == ">=":
            lo = max(lo, n)
        elif op == ">":
            lo = max(lo, n + 1)
        elif op == "<":
            hi = min(hi, n)
        elif op == "<=":
            hi = min(hi, n + 1)
        elif op == "==":
            lo, hi = max(lo, n), min(hi, n + 1)
    if lo >= hi or (lo == minimum and hi == maximum):
        return None
    return lo, hi


def emit_predicate(builder: ir.IRBuilder, t: LiquidTerm, env: Mapping[Name, ir.Value]) -> ir.Value | None:
    if isinstance(t, LiquidLiteralBool):
        return ir.Constant(ir.IntType(1), int(t.value))
    if not isinstance(t, LiquidApp):
        return None
    op, args = t.fun.name, t.args
    if op == "&&" and len(args) == 2:
        a, b = (emit_predicate(builder, arg, env) for arg in args)
        if a is None:
            return b
        if b is None:
            return a
        return builder.and_(a, b)
    # In particular, do not drop unsupported operands from OR or NOT.
    if op not in {"==", "!=", "<", "<=", ">", ">="} or len(args) != 2:
        return None
    values = [env.get(a.name) if isinstance(a, LiquidVar) else None for a in args]
    ty = next((v.type for v in values if v is not None and isinstance(v.type, ir.IntType)), None)
    if ty is None or ty.width <= 1:
        return None
    for i, arg in enumerate(args):
        if isinstance(arg, LiquidLiteralInt) and -(1 << (ty.width - 1)) <= arg.value < (1 << (ty.width - 1)):
            values[i] = ir.Constant(ty, arg.value)
    if any(v is None or v.type != ty for v in values):
        return None
    return builder.icmp_signed(op, values[0], values[1])
