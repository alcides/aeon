from __future__ import annotations

from typing import Any

from aeon.core.terms import Abstraction
from aeon.core.terms import Annotation
from aeon.core.terms import Application
from aeon.core.terms import Hole
from aeon.core.terms import If
from aeon.core.terms import Let
from aeon.core.terms import Literal
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import Var

real_eval = eval


class EvaluationContext:
    variables: dict[str, Any]

    def __init__(self, prev: dict[str, Any] | None = None):
        if prev:
            self.variables = {k: v for (k, v) in prev.items()}
        else:
            self.variables = {}

    def with_var(self, name: str, value: Any):
        v = self.variables.copy()
        v.update({name: value})
        return EvaluationContext(v)

    def get(self, name: str):
        return self.variables[name]


def is_native_var(t: Application):
    return isinstance(t.fun, Var) and t.fun.name == "native"


# pattern match term
def eval(t: Term, ctx: EvaluationContext = EvaluationContext()):
    if isinstance(t, Literal):
        return t.value
    elif isinstance(t, Var):
        return ctx.get(t.name)
    elif isinstance(t, Abstraction):
        return lambda k: eval(t.body, ctx.with_var(t.var_name, k))
    elif isinstance(t, Application):
        f = eval(t.fun, ctx)
        arg = eval(t.arg, ctx)
        # e = real_eval(arg, __globals=ctx.variables) if is_native_var(t) else f(arg)
        e = real_eval(arg, ctx.variables) if is_native_var(t) else f(arg)

        if isinstance(t.fun, Var) and t.fun.name == "native_import":
            globals()[arg] = e
        return e
    elif isinstance(t, Let):
        return eval(t.body, ctx.with_var(t.var_name, eval(t.var_value, ctx)))
    elif isinstance(t, Rec):
        if isinstance(t.var_value, Abstraction):
            fun = t.var_value

            def v(x):
                return eval(
                    fun.body,
                    ctx.with_var(t.var_name, v).with_var(fun.var_name, x),
                )

        else:
            v = eval(t.var_value, ctx)
        return eval(t.body, ctx.with_var(t.var_name, v))
    elif isinstance(t, If):
        c = eval(t.cond, ctx)
        if c:
            return eval(t.then, ctx)
        else:
            return eval(t.otherwise, ctx)
    elif isinstance(t, Annotation):
        return eval(t.expr, ctx)
    elif isinstance(t, Hole):
        args = ", ".join([str(n) for n in ctx.variables])
        print(f"Context ({args})")
        h = input(f"Enter value for hole {t} in Python: ")
        return real_eval(h, ctx.variables)
    assert False
