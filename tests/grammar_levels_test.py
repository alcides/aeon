"""Grammar binder levels survive nesting and lower without name capture."""

import pytest

from aeon.core.liquid import LiquidApp, LiquidVar
from aeon.core.terms import Abstraction, Application, Var
from aeon.core.types import AbstractionType, RefinedType, t_float, t_int, t_string
from aeon.synthesis.modules.tdsyn.bindings import BoundLevel, GrammarScope, open_abstraction
from aeon.synthesis.modules.tdsyn.actions import backward_abs_candidates
from aeon.synthesis.modules.tdsyn.library import visible_vars
from aeon.synthesis.modules.tdsyn.worklist import fresh_hole
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type, synth
from aeon.utils.name import Name


def test_levels_stay_stable_under_scope_extension():
    outer, first = GrammarScope.from_context(TypingContext()).bind("x", t_string)
    inner, second = first.bind("x", t_int)
    assert (outer.level, inner.level) == (0, 1)
    assert outer.lower(first) == outer.lower(second)
    assert inner.lower(second)[1] == t_int
    assert outer.lower(second)[1] == t_string
    assert outer.lower(second)[0].name != inner.lower(second)[0].name
    assert len(visible_vars(second.context)) == 2
    with pytest.raises(ValueError, match="outside"):
        BoundLevel(2).lower(second)
    with pytest.raises(ValueError, match="outside"):
        BoundLevel(-1).lower(second)


def test_sibling_scopes_have_same_level_but_distinct_lowered_identities():
    scope = GrammarScope.from_context(TypingContext())
    left, a = scope.bind("x", t_int)
    right, b = scope.bind("x", t_string)
    assert left == right
    assert left.lower(a)[0].name != right.lower(b)[0].name


def test_reused_signature_binder_cannot_resolve_to_outer_string():
    x = Name("x", 3274)  # Same signature identity implicated in the GP crash.
    convert = Name("toFloat", 0)
    ctx = TypingContext().with_var(convert, AbstractionType(Name("arg", 0), t_int, t_float))
    typ = AbstractionType(x, t_string, AbstractionType(x, t_int, t_float))
    _, outer = fresh_hole(typ, ctx)
    outer_term, outer_holes = backward_abs_candidates(outer, lambda _: False)[0]
    inner_term, inner_holes = backward_abs_candidates(outer_holes[0], lambda _: False)[0]
    inner = inner_holes[0]
    assert outer_term.var_name != inner_term.var_name
    assert inner.context.type_of(outer_term.var_name) == t_string
    assert inner.context.type_of(inner_term.var_name) == t_int
    assert dict(visible_vars(inner.context))[inner_term.var_name] == t_int
    application = Application(Var(convert), Var(inner_term.var_name))
    synth(inner.context, application)  # Used to raise String-vs-Int.
    term = Abstraction(outer_term.var_name, Abstraction(inner_term.var_name, application))
    assert check_type(ctx, term, typ)


def test_opening_renames_dependent_result_and_keeps_external_reference():
    x, v, outside = Name("x", 7), Name("v", 8), Name("outside", 9)
    result = RefinedType(v, t_int, LiquidApp(Name("==", 0), [LiquidVar(v), LiquidVar(x)]))
    ctx = TypingContext().with_var(outside, t_int)
    name, body, extended = open_abstraction(AbstractionType(x, t_int, result), ctx)
    assert body.refinement.args[1] == LiquidVar(name)
    assert extended.type_of(name) == t_int
    assert extended.type_of(outside) == t_int


@pytest.mark.parametrize("module", ["native", "tdsyn"])
def test_initial_abstraction_peeling_uses_distinct_levels(module):
    from aeon.synthesis.modules.native_search import peel_abstractions
    from aeon.synthesis.modules.tdsyn.synthesizer import _peel_abstractions

    x = Name("x", 12)
    typ = AbstractionType(x, t_string, AbstractionType(x, t_int, t_int))
    result = (peel_abstractions if module == "native" else _peel_abstractions)(typ, TypingContext())
    term, holes = result[0], result[-1]
    assert term.var_name != term.body.var_name
    assert holes[0].context.type_of(term.var_name) == t_string
    assert holes[0].context.type_of(term.body.var_name) == t_int


def test_invalid_expansion_does_not_abort_other_grammar_choices(monkeypatch):
    from aeon.errors import CoreTypeCheckingError
    from aeon.synthesis.modules import native_search
    from aeon.synthesis.modules.tdsyn.worklist import PartialAST

    term, hole = fresh_hole(t_int, TypingContext())
    original = native_search.expand_at_hole
    rejected = []

    def expand(partial, hole, replacement, children, depth):
        if not rejected:
            rejected.append(replacement)
            raise CoreTypeCheckingError("invalid grammar production")
        return original(partial, hole, replacement, children, depth)

    monkeypatch.setattr(native_search, "expand_at_hole", expand)
    results = native_search.expansions_for_hole(PartialAST(term, [hole], 0), hole, lambda _: False, prune=False)
    assert rejected
    assert results
    assert all(result.term != rejected[0] for result in results)
