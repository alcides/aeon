from __future__ import annotations

from typing import Any

from aeon.core.terms import Abstraction, RefinementAbstraction, RefinementAbstraction as RefinementAbstraction_alias, RefinementApplication, TypeAbstraction, TypeApplication
from aeon.core.terms import Annotation
from aeon.core.terms import Application
from aeon.core.terms import Hole
from aeon.core.terms import If
from aeon.core.terms import Let
from aeon.core.terms import Literal
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.decorators.api import Metadata
from aeon.llvm.core import LLVMPipeline
from aeon.utils.name import Name

real_eval = eval


class EvaluationContext:
    variables: dict[Name, Any]
    metadata: Metadata | None
    pipeline: LLVMPipeline | None

    def __init__(
        self,
        prev: dict[Name, Any] | None = None,
        metadata: Metadata | None = None,
        pipeline: LLVMPipeline | None = None,
    ):
        if prev:
            self.variables = {k: v for (k, v) in prev.items()}
        else:
            self.variables = {}
        self.metadata = metadata
        self.pipeline = pipeline

    def with_var(self, name: Name, value: Any):
        assert isinstance(name, Name)
        v = self.variables.copy()
        v.update({name: value})
        return EvaluationContext(v, metadata=self.metadata, pipeline=self.pipeline)

    def get(self, name: Name):
        return self.variables[name]


def is_native_var(fun: Any):
    return fun == real_eval


def is_native_import(fun: Term):
    match fun:
        case TypeApplication(t, _):
            return is_native_import(t)
        case Var(Name("native_import", _)):
            return True
        case _:
            return False


# pattern match term
def eval(t: Term, ctx: EvaluationContext = EvaluationContext()) -> Any:
    match t:
        case Literal(value, _):
            return value
        case Var(name):
            return ctx.get(name)
        case Abstraction(var_name, body):
            return lambda k: eval(body, ctx.with_var(var_name, k))
        case Application(fun, arg):
            f = eval(fun, ctx)
            argv = eval(arg, ctx)
            if is_native_var(f):
                assert isinstance(argv, str)

                python_ctx = {str(name): v for name, v in globals().items()}
                python_ctx.update({str(name.name): v for name, v in ctx.variables.items()})
                e = real_eval(argv, python_ctx)
            else:
                e = f(argv)
            if is_native_import(fun):
                globals()[argv] = e
            return e
        case Let(var_name, var_value, body):
            return eval(body, ctx.with_var(var_name, eval(var_value, ctx)))
        case Rec(var_name, _, var_value, body, _, _):
            if isinstance(var_value, Abstraction):
                fun = var_value

                def v_py(x):
                    return eval(
                        fun.body,
                        ctx.with_var(var_name, v_py).with_var(fun.var_name, x),
                    )

                v = v_py

                if ctx.pipeline and ctx.metadata:
                    name_str = var_name.name
                    found_llvm = False
                    for k, meta in ctx.metadata.items():
                        k_name = k.name if isinstance(k, Name) else str(k)
                        if k_name == name_str and (meta.get("cpu") or meta.get("gpu")):
                            found_llvm = True
                            break

                    if found_llvm:
                        try:
                            v_llvm = ctx.pipeline.get_curried_function(var_name,native_fallback=v_py)
                            if v_llvm is not None:
                                v = v_llvm
                        except Exception:
                            v = v_py
                            pass
            else:
                v = eval(var_value, ctx)
            return eval(body, ctx.with_var(var_name, v))
        case If(cond, then, otherwise):
            c = eval(cond, ctx)
            if c:
                return eval(then, ctx)
            else:
                return eval(otherwise, ctx)
        case Annotation(expr, _):
            return eval(expr, ctx)
        case Hole(name):
            args = ", ".join([str(n.name) for n in ctx.variables])
            print(f"Context ({args})")
            h = input(f"Enter value for hole {t} in Python: ")
            return real_eval(h, {str(name): v for name, v in ctx.variables.items()})

        case TypeAbstraction(_, _, body):
            return eval(body, ctx)
        case RefinementAbstraction(_, _, body):
            return eval(body, ctx)
        case TypeApplication(body, _):
            return eval(body, ctx)
        case RefinementApplication(body, _):
            return eval(body, ctx)
        case _:
            assert False, f"Unknown case {t}"
