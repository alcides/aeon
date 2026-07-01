from __future__ import annotations

from typing import Any

from aeon.core.multiplicity import M0
from aeon.core.terms import Abstraction, RefinementAbstraction, RefinementApplication, TypeAbstraction, TypeApplication
from aeon.core.terms import Annotation
from aeon.core.terms import Application
from aeon.core.terms import Hole
from aeon.core.terms import If
from aeon.core.terms import Let
from aeon.core.terms import Literal
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.utils.name import Name
from aeon.backend.contracts import ContractClosure, ContractState, wrap_callable
from aeon.core.types import Type
from aeon.decorators.api import Metadata
from aeon.llvm.core import LLVMPipeline

real_eval = eval


class EvaluationContext:
    variables: dict[Name, Any]
    metadata: Metadata | None
    pipeline: LLVMPipeline | None
    # Optional call-trace sink (instrumented semantics, Fig. 4 of the Contata
    # paper). When non-None, every ``Rec``-bound function call records a
    # ``[name, args, result, parent_index]`` entry here, so a synthesized
    # candidate's behaviour can be observed and its call tree reconstructed (the
    # ``parent_index`` distinguishes a real callee from an unrelated call, e.g.
    # an eagerly-evaluated ``@example`` binding). ``None`` ⇒ zero overhead.
    # ``trace_stack`` holds the indices of the calls currently on the stack and
    # is shared (by reference) with ``trace`` across ``with_var``.
    trace: list | None
    trace_stack: list | None
    contract_state: ContractState | None

    def __init__(
        self,
        prev: dict[Name, Any] | None = None,
        metadata: Metadata | None = None,
        pipeline: LLVMPipeline | None = None,
        trace: list | None = None,
        trace_stack: list | None = None,
        contract_state: ContractState | None = None,
    ):
        if prev:
            self.variables = {k: v for (k, v) in prev.items()}
        else:
            self.variables = {}
        self.metadata = metadata
        self.pipeline = pipeline
        self.trace = trace
        self.trace_stack = trace_stack
        self.contract_state = contract_state

    def with_var(self, name: Name, value: Any):
        assert isinstance(name, Name)
        v = self.variables.copy()
        v.update({name: value})
        if self.contract_state is not None:
            from aeon.backend.contracts import register_runtime_callable

            register_runtime_callable(self.contract_state, name, value)
        return EvaluationContext(
            v,
            metadata=self.metadata,
            pipeline=self.pipeline,
            trace=self.trace,
            trace_stack=self.trace_stack,
            contract_state=self.contract_state,
        )

    def get(self, name: Name):
        return self.variables[name]


def is_native_var(fun: Any):
    return fun is real_eval


def is_native_import(fun: Term):
    match fun:
        case TypeApplication(t, _):
            return is_native_import(t)
        case Var(Name("native_import", _)):
            return True
        case _:
            return False


def _wrap_if_contract(
    fn: Any,
    fn_type: Type | None,
    callee: Name,
    ctx: EvaluationContext,
    *,
    loc,
) -> Any:
    if ctx.contract_state is None or fn_type is None:
        return fn
    return wrap_callable(fn, fn_type, callee, ctx.contract_state, loc=loc)


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
            elif isinstance(f, ContractClosure):
                e = f(argv)
            else:
                e = f(argv)
            if is_native_import(fun):
                globals()[argv] = e
            return e
        case Let(var_name, _, body, _, mult) if mult is M0:
            # Phase 4 — runtime erasure. The linearity check has already
            # verified that ``var_name`` is never referenced at runtime,
            # so we skip evaluating ``var_value`` entirely. ``var_name``
            # is bound to ``None`` only as a tripwire — any reference
            # would raise immediately, surfacing a missed check.
            return eval(body, ctx.with_var(var_name, None))
        case Let(var_name, var_value, body):
            value = eval(var_value, ctx)
            return eval(body, ctx.with_var(var_name, value))
        case Rec(var_name, _, _, body, _, _, mult) if mult is M0:
            # Phase 4 — same erasure for ``Rec``. ``var_value`` may be a
            # recursive lambda that's only meaningful at type level.
            return eval(body, ctx.with_var(var_name, None))
        case Rec(_, _, _, _, _, _) if t.mutual_group_id is not None:
            # Mutually-recursive group: collect the contiguous run of members
            # sharing this group id, then tie all their knots over a single
            # shared context so each member's body can call any sibling.
            gid = t.mutual_group_id
            members: list[Rec] = []
            cur: Term = t
            while isinstance(cur, Rec) and cur.mutual_group_id == gid:
                members.append(cur)
                cur = cur.body
            final_body = cur

            group_ctx = EvaluationContext(
                ctx.variables,
                metadata=ctx.metadata,
                pipeline=ctx.pipeline,
                trace=ctx.trace,
                trace_stack=ctx.trace_stack,
                contract_state=ctx.contract_state,
            )
            for m in members:
                inner_value = m.var_value
                while isinstance(inner_value, (TypeAbstraction, RefinementAbstraction)):
                    inner_value = inner_value.body
                if isinstance(inner_value, Abstraction):

                    def make_closure(fun: Abstraction, fname: Name, ftype: Type):
                        def v(x):
                            tr = group_ctx.trace
                            if tr is None:
                                return eval(fun.body, group_ctx.with_var(fun.var_name, x))
                            st = group_ctx.trace_stack
                            idx = len(tr)
                            tr.append([fname, (x,), None, st[-1] if st else -1])
                            st.append(idx)
                            try:
                                result = eval(fun.body, group_ctx.with_var(fun.var_name, x))
                            finally:
                                st.pop()
                            tr[idx][2] = result
                            return result

                        return _wrap_if_contract(v, ftype, fname, group_ctx, loc=fun.loc)

                    group_ctx.variables[m.var_name] = make_closure(inner_value, m.var_name, m.var_type)
                else:
                    # Non-lambda mutual binding: evaluate in the shared context
                    # (closures resolve siblings lazily) and patch the cell.
                    group_ctx.variables[m.var_name] = None
                    group_ctx.variables[m.var_name] = eval(m.var_value, group_ctx)
            return eval(final_body, group_ctx)
        case Rec(var_name, var_type, var_value, body, _, _):
            found_llvm = False
            if ctx.pipeline and ctx.metadata:
                for k, v in ctx.metadata.items():
                    k_name = k.name if isinstance(k, Name) else str(k)
                    if k_name == var_name.name and v.get("llvm"):
                        found_llvm = True
                        break

            if found_llvm:
                try:
                    v = ctx.pipeline.get_curried_function(var_name)
                    if v is not None:
                        return eval(body, ctx.with_var(var_name, v))
                except Exception:
                    pass

            # Peel off TypeAbstraction/RefinementAbstraction wrappers introduced by
            # elaboration so the recursion-tying trick still applies to polymorphic
            # functions (e.g. ``def length : forall a, ... = fun l => ... (length tl) ...``).
            inner_value = var_value
            while isinstance(inner_value, (TypeAbstraction, RefinementAbstraction)):
                inner_value = inner_value.body

            if isinstance(inner_value, Abstraction):
                fun = inner_value

                def v(x):
                    rec_ctx = ctx.with_var(var_name, v).with_var(fun.var_name, x)
                    tr = ctx.trace
                    if tr is None:
                        return eval(fun.body, rec_ctx)
                    st = ctx.trace_stack
                    idx = len(tr)
                    tr.append([var_name, (x,), None, st[-1] if st else -1])
                    st.append(idx)
                    try:
                        result = eval(fun.body, rec_ctx)
                    finally:
                        st.pop()
                    tr[idx][2] = result
                    return result

                v = _wrap_if_contract(v, var_type, var_name, ctx, loc=t.loc)
            else:
                # General recursion for non-lambda values (e.g. instance
                # dictionaries whose default methods reference sibling
                # methods, making the dict refer to itself). Bind
                # ``var_name`` to a placeholder cell, evaluate the value in
                # that context, then patch the cell in place. Closures built
                # while evaluating ``var_value`` capture this context object
                # and resolve ``var_name`` lazily at call time, so the patch
                # ties the recursive knot.
                rec_ctx = ctx.with_var(var_name, None)
                v = eval(var_value, rec_ctx)
                rec_ctx.variables[var_name] = v
            return eval(body, ctx.with_var(var_name, v))
        case If(cond, then, otherwise):
            c = eval(cond, ctx)
            if c:
                return eval(then, ctx)
            else:
                return eval(otherwise, ctx)
        case Annotation(expr, ty):
            value = eval(expr, ctx)
            if ctx.contract_state is not None:
                from aeon.backend.contracts import check_return_refinement

                check_return_refinement(
                    ty,
                    value,
                    ctx.contract_state,
                    callee=Name("<annotation>", 0),
                    loc=expr.loc,
                )
            return value
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


def eval_with_trace(t: Term, ctx: EvaluationContext = EvaluationContext()) -> tuple[Any, list]:
    """Instrumented evaluation (Contata, Fig. 4): evaluate ``t`` and return
    ``(value, trace)`` where ``trace`` is the list of ``[name, args, result,
    parent_index]`` entries for every ``Rec``-bound function call made during
    evaluation (``parent_index`` is the trace index of the enclosing call, or
    ``-1`` for a top-level call). Used by co-synthesis to observe a candidate's
    behaviour, reconstruct its call tree, and blame failing inputs."""
    sink: list = []
    traced = EvaluationContext(
        ctx.variables,
        metadata=ctx.metadata,
        pipeline=ctx.pipeline,
        trace=sink,
        trace_stack=[],
        contract_state=ctx.contract_state,
    )
    value = eval(t, traced)
    return value, sink
