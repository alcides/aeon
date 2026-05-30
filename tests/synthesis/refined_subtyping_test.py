"""Tests for refined-type subtyping in the synthesis grammar (issue #312).

Stage 1 wires refined classes that share a base into a single linear
inheritance chain (a linear extension of the subtype partial order), deciding
subtyping with a purely syntactic literal-interval-containment rule. This lets
geneticengine reach narrower-refined literals from wider-refined slots.
"""

from __future__ import annotations

from geneticengine.grammar import extract_grammar

from aeon.core.equality import canonicalize_type
from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.core.types import RefinedType, t_int
from aeon.synthesis.grammar.grammar_generation import (
    create_literal_ref_nodes,
    extract_all_types,
)
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

X = Name("x", 0)


def ti(type_info, ty):
    """``type_info`` is keyed on alpha-equivalence canonical forms (#311)."""
    return type_info[canonicalize_type(ty)]


def ref(op: str, c: int) -> RefinedType:
    """{x:Int | x OP c}."""
    return RefinedType(X, t_int, LiquidApp(Name(op, 0), [LiquidVar(X), LiquidLiteralInt(c)]))


def conj(*atoms: LiquidApp) -> LiquidApp:
    expr = atoms[0]
    for a in atoms[1:]:
        expr = LiquidApp(Name("&&", 0), [expr, a])
    return expr


def atom(op: str, c: int) -> LiquidApp:
    return LiquidApp(Name(op, 0), [LiquidVar(X), LiquidLiteralInt(c)])


def build_grammar_and_lits(types, ctx):
    """Mirror create_grammar's tail: extract types, build refined literals,
    and produce a usable grammar. Returns (type_info, literals, grammar)."""
    type_info = extract_all_types(list(types), ctx)
    literals = create_literal_ref_nodes(type_info)
    nodes = list(set(type_info.values())) + literals
    grammar = extract_grammar(nodes, ti(type_info, t_int)).usable_grammar()
    return type_info, literals, grammar


def literal_for(literals, refined_class):
    """The literal dataclass whose direct parent is the given refined class."""
    for lit in literals:
        if lit.__bases__[0] is refined_class:
            return lit
    return None


def test_narrow_reachable_from_wide():
    """{x:Int|x>5} (narrow) must be reachable from a {x:Int|x>0} (wide) slot."""
    wide = ref(">", 0)
    narrow = ref(">", 5)
    ctx = TypingContext([])
    type_info, literals, g = build_grammar_and_lits([wide, narrow, t_int], ctx)

    wide_c = ti(type_info, wide)
    narrow_c = ti(type_info, narrow)
    narrow_lit = literal_for(literals, narrow_c)
    wide_lit = literal_for(literals, wide_c)

    assert narrow_lit is not None
    assert wide_lit is not None

    # Sound: a value of x>5 satisfies x>0.
    assert g.is_reachable(wide_c, narrow_lit) is True
    # Unsound direction must NOT hold: a value of x>0 does not satisfy x>5.
    assert g.is_reachable(narrow_c, wide_lit) is False


def test_two_sided_interval_containment():
    """{x | 2<=x<=8} must be reachable from {x | 0<=x<=10}."""
    wide = RefinedType(X, t_int, conj(atom(">=", 0), atom("<=", 10)))
    narrow = RefinedType(X, t_int, conj(atom(">=", 2), atom("<=", 8)))
    ctx = TypingContext([])
    type_info, literals, g = build_grammar_and_lits([wide, narrow, t_int], ctx)

    wide_lit = literal_for(literals, ti(type_info, wide))
    narrow_lit = literal_for(literals, ti(type_info, narrow))

    assert g.is_reachable(ti(type_info, wide), narrow_lit) is True
    assert g.is_reachable(ti(type_info, narrow), wide_lit) is False


def test_equivalence_cycle_collapses():
    """Two intervals denoting the same set collapse to one class, no crash.

    Over the syntactic-interval analyzer, x>=0 && x<=10 and 0<=x<=10 written
    differently produce the same interval and must collapse to a single
    canonical chain class.
    """
    a = RefinedType(X, t_int, conj(atom(">=", 0), atom("<=", 10)))
    # Same interval, atoms in the opposite order.
    b = RefinedType(X, t_int, conj(atom("<=", 10), atom(">=", 0)))
    ctx = TypingContext([])
    type_info, literals, g = build_grammar_and_lits([a, b, t_int], ctx)

    # Both refined keys must point at the SAME canonical chain class.
    assert ti(type_info, a) is ti(type_info, b)


def test_three_chain_plus_antichain_no_mro_error():
    """A 3-element chain together with an incomparable refinement must build
    without raising an MRO error."""
    # Chain: x>0  superset of  x>5  superset of  x>10
    c0 = ref(">", 0)
    c5 = ref(">", 5)
    c10 = ref(">", 10)
    # Antichain element relative to the above (a disjoint upper-bounded set).
    upper = ref("<", -3)
    ctx = TypingContext([])
    # Should not raise "Cannot create a consistent method resolution order".
    type_info, literals, g = build_grammar_and_lits([c0, c5, c10, upper, t_int], ctx)

    # The chain is linear: x>10 reachable from x>5 reachable from x>0.
    lit10 = literal_for(literals, ti(type_info, c10))
    lit5 = literal_for(literals, ti(type_info, c5))
    assert g.is_reachable(ti(type_info, c0), lit10) is True
    assert g.is_reachable(ti(type_info, c0), lit5) is True
    assert g.is_reachable(ti(type_info, c5), lit10) is True
    # The antichain element is not below the chain.
    lit_upper = literal_for(literals, ti(type_info, upper))
    assert g.is_reachable(ti(type_info, c0), lit_upper) is False


def test_ctx_none_skips_subtyping():
    """Without a context, no chain is built: refined classes stay attached to
    the base class only (legacy behaviour preserved)."""
    wide = ref(">", 0)
    narrow = ref(">", 5)
    type_info = extract_all_types([wide, narrow, t_int])

    # No subtyping chain is built: the two refined classes are unrelated
    # (neither inherits from the other). Each inherits directly from a base
    # class named æInt.
    assert ti(type_info, narrow) not in ti(type_info, wide).__mro__
    assert ti(type_info, wide) not in ti(type_info, narrow).__mro__
    assert ti(type_info, wide).__bases__[0].__name__ == "æInt"
    assert ti(type_info, narrow).__bases__[0].__name__ == "æInt"
