"""Form B existentials replaced ANF — focused regression tests.

ANF historically rewrote every non-Var argument into `let _anf = arg in f _anf`
so that `synth(Application)` could substitute a name into the result type.
The pass is gone now (commit ``Phase 0 spike (5/N)`` deleted the module);
the synthesised binder lives in the *type* via Form B existentials.

These tests exercise that path directly with hand-built core terms whose
applications have non-trivial arguments (e.g. ``id (id 0)``), confirming
that:

1. `synth(Application)` produces a constraint that solves;
2. the resulting type carries an `ExistentialType` binder;
3. a refinement on the function's return type that mentions the parameter
   name survives the binder substitution and is provable.
"""

from __future__ import annotations

from hypothesis import example, given, strategies as st
import pytest

from aeon.compilation.session import CompilationSession
from aeon.core.bind import bind_ids
from aeon.core.parser import parse_term
from aeon.core.terms import Application, Term
from aeon.core.types import AbstractionType, ExistentialType, RefinedType, top
from aeon.elaboration.context import build_typing_context
from aeon.prelude.prelude import typing_vars
from aeon.sugar.lowering import lower_to_core_context
from aeon.typechecking.typeinfer import check_type, synth


def _ctx_and_term(source: str) -> tuple:
    elabcontext = build_typing_context(typing_vars)
    typing_ctx = lower_to_core_context(elabcontext)
    core_ast = parse_term(source)
    typing_ctx, core_ast = bind_ids(typing_ctx, core_ast)
    # NOTE: deliberately skip `ensure_anf`.
    return typing_ctx, core_ast


def _has_non_var_arg(t: Term) -> bool:
    """True iff some `Application` anywhere in `t` has a non-Var/non-Literal arg."""
    from aeon.core.terms import Abstraction, If, Let, Literal, Rec, Var

    match t:
        case Application(fun, arg):
            if not isinstance(arg, (Var, Literal)):
                return True
            return _has_non_var_arg(fun) or _has_non_var_arg(arg)
        case Let(_, val, body) | Rec(_, _, val, body, _, _):
            return _has_non_var_arg(val) or _has_non_var_arg(body)
        case Abstraction(_, body):
            return _has_non_var_arg(body)
        case If(c, th, el):
            return _has_non_var_arg(c) or _has_non_var_arg(th) or _has_non_var_arg(el)
        case _:
            return False


def test_application_with_non_var_arg_typechecks_without_anf():
    """`id (id 0)` with `id : (x:Int) -> Int` type-checks against `Top`
    even when the inner argument is a non-trivial `Application` and we never
    run the ANF pass."""
    src = r"""
        let id : (x:Int) -> Int = fun x => x in
        id (id 0)
    """.strip()
    ctx, term = _ctx_and_term(src)
    assert _has_non_var_arg(term), "Test sanity: outer call should keep its non-Var arg without ANF"
    assert check_type(ctx, term, top), "Term should type-check at Top"


def test_synth_application_emits_existential_for_non_var_arg():
    """Synth of `id (id 0)` returns an `ExistentialType` because the outer
    application's argument is itself an `Application`, not a `Var`/`Literal`."""
    src = r"""
        let id : (x:Int) -> Int = fun x => x in
        id (id 0)
    """.strip()
    ctx, term = _ctx_and_term(src)
    _, ty = synth(ctx, term)
    assert isinstance(ty, ExistentialType), f"Expected ExistentialType, got {type(ty).__name__}: {ty}"
    assert ty.binders, "Existential should have at least one binder"
    _, bt = ty.binders[0]
    assert isinstance(bt, (RefinedType, AbstractionType)), f"Binder type should be Refined/Abstraction, got {bt}"


@example(values=[1, 2, 3], nested=True)
@example(values=[0, 1, 1], nested=False)
@example(values=[1, 0, 1], nested=False)
@example(values=[1, 1, 0], nested=False)
@given(
    values=st.lists(st.integers(min_value=-3, max_value=3), min_size=2, max_size=5),
    nested=st.booleans(),
)
def test_every_nested_argument_must_satisfy_its_precondition(values: list[int], nested: bool):
    """A failed call cannot use its contradictory result to justify earlier arguments."""
    names = [f"arg{i}" for i in range(len(values))]
    signature = " -> ".join([*(f"({name}:{{v:Int | v > 0}})" for name in names), "Int"])
    body = "".join(f"fun {name} => " for name in names) + names[-1]
    arguments = [f"(identity ({value}))" if nested else f"({value})" for value in values]
    source = f"""
        let identity : (x:Int) -> {{r:Int | r == x}} = fun x => x in
        let positive : (x:{{v:Int | v > 0}}) -> {{r:Int | (r == x) && (r > 0)}} = fun x => x in
        let consume : {signature} = {body} in
        consume {" ".join(f"(positive {argument})" for argument in arguments)}
    """
    with CompilationSession().activate():
        ctx, term = _ctx_and_term(source)
        assert check_type(ctx, term, top) == all(value > 0 for value in values)


@pytest.mark.parametrize("later, accepted", [(1, False), (2, False), (3, True)])
def test_later_arguments_can_depend_on_checked_earlier_arguments(later: int, accepted: bool):
    """An earlier existential witness still scopes the later argument's obligation."""
    source = f"""
        let identity : (x:Int) -> {{r:Int | r == x}} = fun x => x in
        let increasing : (x:Int) -> (y:{{v:Int | v > x}}) -> {{r:Int | r > x}} =
            fun x => fun y => y in
        increasing (identity 2) (identity {later})
    """
    with CompilationSession().activate():
        ctx, term = _ctx_and_term(source)
        assert check_type(ctx, term, top) == accepted
