from __future__ import annotations

from typing import Any

from aeon.core.terms import Abstraction, TypeAbstraction, TypeApplication
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


def is_native_var(fun: Term):
    match fun:
        case TypeApplication(t, _):
            return is_native_var(t)
        case Var("native"):
            return True
        case _:
            return False


def is_native_import(fun: Term):
    return isinstance(fun, Var) and fun.name == "native_import"


# pattern match term
def eval(t: Term, ctx: EvaluationContext = EvaluationContext()) -> Any:
    match t:
        case Literal(value, _):
            return value
        case Var(name):
            return ctx.get(str(name))
        case Abstraction(var_name, body):
            return lambda k: eval(body, ctx.with_var(var_name, k))
        case Application(fun, arg):
            f = eval(fun, ctx)
            argv = eval(arg, ctx)
            if is_native_var(fun):
                assert isinstance(argv, str)
                e = real_eval(argv, ctx.variables)
            else:
                e = f(argv)
            if is_native_import(fun):
                globals()[argv] = e
            return e
        case Let(var_name, var_value, body):
            return eval(body, ctx.with_var(var_name, eval(var_value, ctx)))
        case Rec(var_name, _, var_value, body):
            if isinstance(var_value, Abstraction):
                fun = var_value

                def v(x):
                    return eval(
                        fun.body,
                        ctx.with_var(var_name, v).with_var(fun.var_name, x),
                    )

            else:
                v = eval(var_value, ctx)
            return eval(t.body, ctx.with_var(t.var_name, v))
        case If(cond, then, otherwise):
            c = eval(cond, ctx)
            if c:
                return eval(then, ctx)
            else:
                return eval(otherwise, ctx)
        case Annotation(expr, _):
            return eval(expr, ctx)
        case Hole(name):
            args = ", ".join([str(n) for n in ctx.variables])
            print(f"Context ({args})")
            h = input(f"Enter value for hole {t} in Python: ")
            return real_eval(h, ctx.variables)

        case TypeAbstraction(_, _, body):
            return eval(body, ctx)
        case TypeApplication(body, _):
            return eval(body, ctx)
    assert False
