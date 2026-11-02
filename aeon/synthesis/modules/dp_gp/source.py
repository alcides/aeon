"""Opt-in declaration, scalar IR extraction and exact bounded input contracts."""

import z3

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidVar
from aeon.core.terms import Abstraction, Literal, Var
from aeon.core.types import AbstractionType, RefinedType, t_int
from aeon.decorators.api import metadata_update_by_name
from aeon.sugar.program import SLiteral, SVar
from aeon.synthesis.api import UnsupportedSynthesisGoal
from aeon.synthesis.modules.dp_gp.checking import counterexample
from aeon.synthesis.modules.dp_gp.expressions import Expr, applications, extract, function, literal, variable
from aeon.synthesis.modules.dp_gp.model import Problem


def dp_decorator(dec, fun_name, typing_ctx, program, metadata):
    args = dec.macro_args
    if (
        len(args) != 3
        or not isinstance(args[0], SVar)
        or any(not isinstance(a, SLiteral) or type(a.value) is not int or a.value < 0 for a in args[1:])
    ):
        raise UnsupportedSynthesisGoal("@dp_gp(reference, max_first_input, max_second_input) needs a name and bounds")
    return metadata_update_by_name(metadata, fun_name, {"dp_gp": (args[0].name.name, args[1].value, args[2].value)})


def liquid(term, binder):
    if isinstance(term, (LiquidLiteralInt, LiquidLiteralBool)):
        return literal(term.value)
    if isinstance(term, LiquidVar) and term.name == binder:
        return variable(0)
    if (
        isinstance(term, LiquidApp)
        and term.fun.id == 0
        and term.fun.name in ("&&", "||", "==", "!=", "<", "<=", ">", ">=", "+", "-", "*", "!")
    ):
        return Expr(term.fun.name, tuple(liquid(a, binder) for a in term.args))
    raise UnsupportedSynthesisGoal("dp_gp input contracts must be closed integer intervals")


def unpack(definition, bounds, deadline, target=False):
    body, ty = definition.var_value, definition.var_type
    params = []
    for bound in bounds:
        if not isinstance(body, Abstraction) or not isinstance(ty, AbstractionType):
            raise UnsupportedSynthesisGoal("dp_gp requires exactly two scalar parameters")
        param_type = ty.var_type
        if target:
            if not isinstance(param_type, RefinedType) or param_type.type != t_int:
                raise UnsupportedSynthesisGoal("dp_gp target parameters require explicit 0..bound refinements")
            x = z3.Int("input")
            if (
                counterexample(
                    liquid(param_type.refinement, param_type.name).symbolic((x,)) != z3.And(x >= 0, x <= bound),
                    (x,),
                    deadline,
                )
                is not None
            ):
                raise UnsupportedSynthesisGoal("dp_gp annotation bounds must equal the declared input intervals")
        elif param_type != t_int:
            raise UnsupportedSynthesisGoal("dp_gp reference parameters must be unrestricted Int")
        params.append(body.var_name)
        body, ty = body.body, ty.type
    if (ty.type if isinstance(ty, RefinedType) else ty) != t_int:
        raise UnsupportedSynthesisGoal("dp_gp supports optimum values, not witnesses or tie contracts")
    return params, body


def problem_from_source(reference, bounds, definitions, deadline):
    params, body = unpack(reference, bounds, deadline)
    head, args = applications(body)
    if not isinstance(head, Var) or head.name.name != "DP_reference" or len(args) != 16:
        raise UnsupportedSynthesisGoal("dp_gp reference must directly call the finite additive DP.reference interface")
    bindings = {n: variable(i) for i, n in enumerate(params)}
    if extract(args[0], definitions, bindings) != variable(0):
        raise UnsupportedSynthesisGoal("dp_gp reference fuel must be its first input")
    if any(not isinstance(a, Literal) or type(a.value) is not int for a in args[12:]):
        raise UnsupportedSynthesisGoal("dp_gp base solution and empty-result floor must be Int literals")
    return Problem(
        tuple(extract(a, definitions, bindings) for a in args[1:4]),
        function(args[4], 4, definitions),
        tuple(function(a, 4, definitions) for a in args[5:8]),
        tuple(function(a, 4, definitions) for a in args[8:11]),
        function(args[11], 3, definitions),
        tuple(a.value for a in args[12:15]),
        args[15].value,
        bounds,
    )
