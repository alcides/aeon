"""Exact logical bodies for the Array library's small, pure native operations."""

from aeon.core.liquid import LiquidApp, LiquidTerm, LiquidVar
from aeon.core.terms import Application, Literal, RefinementApplication, Term, TypeApplication, Var
from aeon.core.types import RefinedType, Type, TypeConstructor, t_int
from aeon.utils.name import Name


ARRAY_CONSTRUCTORS = {f"Array_mk_{n}" for n in (1, 2, 4, 8, 16, 32)} | {"Array_mk_concat"}
ARRAY_OPERATIONS = ARRAY_CONSTRUCTORS | {"Array_get", "Array_size"}


def array_logical_body(
    name: Name, params: list[Name], types: list[Type], result: Type, body: Term
) -> LiquidTerm | None:
    """Recognize implementations, not just names: a shadowed helper stays ordinary.

    These operations preserve contents and can be modeled as finite sequences.
    Other native expressions remain opaque; no Python is evaluated here.
    """

    def base(ty: Type) -> Type:
        return base(ty.type) if isinstance(ty, RefinedType) else ty

    def array(ty: Type) -> bool:
        ty = base(ty)
        return isinstance(ty, TypeConstructor) and ty.name.name == "Array" and len(ty.args) == 1

    args: list[LiquidTerm] = [LiquidVar(p) for p in params]
    while isinstance(body, (TypeApplication, RefinementApplication)):
        body = body.body
    if name.name == "Array_size" and len(params) == 1 and array(types[0]) and base(result) == t_int:
        if isinstance(body, Var) and body.name == Name("uninterpreted", 0):
            return LiquidApp(Name("__array_size", 0), args)
    if not isinstance(body, Application) or not isinstance(body.arg, Literal):
        return None
    head = body.fun
    while isinstance(head, (TypeApplication, RefinementApplication)):
        head = head.body
    if not isinstance(head, Var) or head.name != Name("native", 0):
        return None
    code = body.arg.value
    if name.name in ARRAY_CONSTRUCTORS - {"Array_mk_concat"} and array(result):
        arity = int(name.name.rsplit("_", 1)[1])
        if len(params) == arity and code == "[" + ", ".join(p.name for p in params) + "]":
            return LiquidApp(Name("__array_literal", 0), args)
    if name.name == "Array_mk_concat" and len(params) == 2 and all(array(t) for t in [*types, result]):
        if code == f"{params[0].name} + {params[1].name}":
            return LiquidApp(Name("__array_concat", 0), args)
    if name.name == "Array_get" and len(params) == 2 and array(types[0]) and base(types[1]) == t_int:
        if code == f"{params[0].name}[{params[1].name}]":
            return LiquidApp(Name("__array_get", 0), args)
    return None
