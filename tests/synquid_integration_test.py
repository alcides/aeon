"""Whole-program synthesis retains datatype measures and termination checking."""

from aeon.core.substitutions import substitution
from aeon.core.terms import Application, Let, Var
from aeon.core.types import top
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.identification import get_holes_info, incomplete_functions_and_holes
from aeon.synthesis.modules.synquid.synthesizer import SynquidSynthesizer
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name, fresh_counter
from tests.driver import check_and_return_core


def test_recursive_datatype_synthesis_verifies_measure_and_termination():
    source = """
    inductive Nat
    | zero : {n:Nat | size n = 0}
    | succ (p:{q:Nat | size q >= 0}) : {n:Nat | size n = size p + 1}
    + size (n:Nat) : Int

    @allow_recursion
    def build (n:Int | n >= 0) : {r:Nat | size r = n} decreasing_by [n] :=
        if n = 0 then Nat.zero else
            let m : {v:Int | v >= 0 && v = n - 1} := n - 1;
            Nat.succ (?hole : {q:Nat | size q = m});
    """
    program, ctx, ectx, metadata = check_and_return_core(source)
    targets = incomplete_functions_and_holes(ctx, program)
    function, (hole,) = targets[0]
    metadata[function]["synquid_max_level"] = 1
    backend = SynquidSynthesizer()
    mapping = synthesize_holes(ctx, ectx, program, targets, metadata, backend, budget=10, ui=SilentSynthesisUI())
    candidate = mapping[hole]
    assert isinstance(candidate, Application) and candidate.fun == Var(function)
    assert isinstance(candidate.arg, Var) and candidate.arg.name.name == "m"
    assert check_type(ctx, substitution(program, candidate, hole), top)
    assert backend.stats.full_validations >= 1

    # Adding an unused, non-decreasing recursive call preserves the result's
    # value/refinement but must fail whole-program termination validation.
    _, hole_context = get_holes_info(ctx, program, top, targets, refined_types=True)[hole]
    n = next(n for n, _ in hole_context.concrete_vars() if n.name == "n")
    looping = Let(Name("ignored", fresh_counter.fresh()), Application(Var(function), Var(n)), candidate)
    assert not check_type(ctx, substitution(program, looping, hole), top)
