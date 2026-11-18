from __future__ import annotations

from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.core.parser import parse_type
from aeon.core.types import AbstractionType, LiquidHornApplication, RefinedType, TypeConstructor, TypeVar, t_int
from aeon.typechecking.qualifiers import extract_qualifier_atoms
from aeon.utils.ctx_helpers import build_context
from aeon.utils.name import Name
from aeon.verification.horn import adapt_qualifier_to_hole, build_initial_assignment, build_qualifier_candidates
from aeon.verification.vcs import LiquidConstraint


def test_extract_qualifier_atoms_from_context_refinement():
    ty = parse_type("{v:Int | v <= 42}")
    ctx = build_context({Name("x", 0): ty})
    atoms = extract_qualifier_atoms(ctx)
    assert len(atoms) >= 1
    assert any(
        isinstance(a, LiquidApp)
        and a.fun.name == "<="
        and any(isinstance(x, LiquidLiteralInt) and x.value == 42 for x in a.args)
        for a in atoms
    )


def test_set_measure_adds_one_membership_template():
    element = TypeVar(Name("a", 0))
    list_a = TypeConstructor(Name("List", 0), [element])
    set_a = TypeConstructor(Name("Set", 0), [element])
    ctx = build_context(
        {
            Name("x", 0): element,
            Name("xs", 0): list_a,
            Name("elems", 0): AbstractionType(Name("ys", 0), list_a, set_a),
        }
    )
    atoms = extract_qualifier_atoms(ctx)
    membership = [
        atom
        for atom in atoms
        if isinstance(atom, LiquidApp)
        and atom.fun.name == "Set_mem"
        and len(atom.args) == 2
        and isinstance(atom.args[0], LiquidVar)
        and atom.args[0].name.name == "x"
    ]
    assert len(membership) == 1
    container = membership[0].args[1]
    assert isinstance(container, LiquidApp)
    assert container.fun.name == "elems"
    assert [arg.name.name for arg in container.args if isinstance(arg, LiquidVar)] == ["xs"]


def test_extract_qualifier_atoms_goal_type():
    ctx = build_context({})
    goal = parse_type("{w:Int | w > 10}")
    atoms = extract_qualifier_atoms(ctx, goal_type=goal)
    assert any(
        isinstance(a, LiquidApp)
        and a.fun.name == ">"
        and any(isinstance(x, LiquidLiteralInt) and x.value == 10 for x in a.args)
        for a in atoms
    )


def test_qualifier_wired_into_horn_candidates():
    ty = parse_type("{v:Int | v <= 42}")
    assert isinstance(ty, RefinedType)
    vname = ty.name
    ctx = build_context({Name("x", 0): ty})
    atoms = extract_qualifier_atoms(ctx)
    hole = LiquidHornApplication(Name("k", 0), [(LiquidVar(vname), t_int)])
    adapted = adapt_qualifier_to_hole(hole, next(iter(atoms)))
    assert adapted is not None
    assert LiquidLiteralInt(42) in getattr(adapted, "args", [])

    assign = build_initial_assignment(
        LiquidConstraint(LiquidHornApplication(Name("k", 0), [(LiquidVar(vname), t_int)])),
        typing_ctx=ctx,
        qualifier_atoms=atoms,
    )
    k = Name("k", 0)
    assert k in assign
    assert len(assign[k]) > 30
    assert any(
        isinstance(c, LiquidApp)
        and c.fun.name == "<="
        and any(isinstance(x, LiquidLiteralInt) and x.value == 42 for x in c.args)
        for c in assign[k]
    )


def test_build_qualifier_candidates_empty_atoms():
    hole = LiquidHornApplication(Name("k", 0), [(LiquidVar(Name("x", 0)), t_int)])
    assert build_qualifier_candidates(None, hole, frozenset()) == []
