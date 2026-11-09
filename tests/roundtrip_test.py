"""Generate surface ASTs directly, then check print/parse structural roundtrips.

These are syntactically valid trees, not necessarily closed or well typed. Core
and elaboration-only nodes are outside this property, as are type applications
which the display printer intentionally erases. Names use pre-resolution IDs;
refined parameter binders are already aligned as the printer requires.
"""

from dataclasses import fields, is_dataclass
from typing import Any

import pytest
from hypothesis import given, note, strategies as st

from aeon.core.multiplicity import Multiplicity
from aeon.core.types import Kind, ArrowKind
from aeon.sugar.ast_helpers import st_bool, st_float, st_int, st_string
from aeon.sugar.parser import parse_expression, parse_type
from aeon.sugar.program import (
    SAbstraction,
    SAnnotation,
    SAnonConstructor,
    SApplication,
    SBy,
    SHole,
    SIf,
    SLet,
    SLiteral,
    SQualifiedVar,
    SRec,
    STerm,
    STypeAbstraction,
    SVar,
)
from aeon.sugar.stypes import (
    SAbstractionType,
    SRefinedType,
    SType,
    STypeConstructor,
    STypePolymorphism,
    STypeVar,
)
from aeon.utils.name import Name
from aeon.utils.pprint import pretty_print_sterm, pretty_print_stype, sterm_pretty, stype_pretty


# A prefix avoids keywords and lexer-reserved prefixes such as true/false.
names = st.from_regex(r"v[a-zA-Z0-9_]{0,7}", fullmatch=True).map(Name)
operators = st.sampled_from(["+", "-", "*", "/", "%", "==", "!=", "<", "<=", ">", ">=", "&&", "||"])
multiplicities = st.sampled_from(list(Multiplicity))
kinds = st.recursive(st.sampled_from(list(Kind)), lambda child: st.builds(ArrowKind, child, child), max_leaves=4)
literals = st.one_of(
    st.builds(SLiteral, st.integers(), st.just(st_int)),
    st.builds(SLiteral, st.booleans(), st.just(st_bool)),
    st.builds(SLiteral, st.floats(allow_nan=False, allow_infinity=False), st.just(st_float)),
    st.builds(SLiteral, st.text(max_size=30), st.just(st_string)),
)


def binary(operator: str, left: STerm, right: STerm) -> STerm:
    return SApplication(SApplication(SVar(Name(operator)), left), right)


predicates = st.recursive(
    st.one_of(literals, st.builds(SVar, names)),
    lambda child: st.builds(binary, operators, child, child),
    max_leaves=6,
)


def function_type(name: Name, domain: SType, codomain: SType, multiplicity: Multiplicity) -> SType:
    binder = domain.name if isinstance(domain, SRefinedType) else name
    return SAbstractionType(binder, domain, codomain, multiplicity=multiplicity)


@st.composite
def compound_types(draw: st.DrawFn, child: st.SearchStrategy[SType]) -> SType:
    return draw(
        st.one_of(
            st.builds(
                STypeConstructor, st.sampled_from([Name("List"), Name("Pair")]), st.lists(child, min_size=1, max_size=2)
            ),
            st.builds(SRefinedType, names, child, predicates),
            st.builds(function_type, names, child, child, multiplicities),
            st.builds(STypePolymorphism, names, kinds, child),
        )
    )


types = st.recursive(
    st.one_of(
        st.sampled_from([st_int, st_bool, st_float, st_string, STypeConstructor(Name("Unit", 0))]),
        st.builds(STypeVar, names),
    ),
    compound_types,
    max_leaves=6,
)


def recursive_binding(name: Name, ty: SType, value: STerm, body: STerm, multiplicity: Multiplicity) -> STerm:
    binder = ty.name if isinstance(ty, SRefinedType) else name
    return SRec(binder, ty, value, body, multiplicity=multiplicity)


leaves = st.one_of(
    literals,
    st.builds(SVar, names),
    st.builds(SVar, operators.map(Name)),
    st.builds(SHole, names),
    st.builds(SQualifiedVar, st.sampled_from(["Math", "List", "Module.Nested"]), names),
    st.builds(SAnonConstructor, st.sampled_from(["nil", "cons", "some"])),
    st.builds(
        SBy, st.lists(st.sampled_from(["assumption", "constructor", "split"]), min_size=1, max_size=3).map(tuple)
    ),
)


def compound_terms(child: Any) -> dict[str, Any]:
    return {
        "application": st.builds(SApplication, child, child),
        "operator": st.builds(binary, operators, child, child),
        "lambda": st.builds(SAbstraction, names, child),
        "let": st.builds(SLet, names, child, child, multiplicity=multiplicities),
        "rec": st.builds(recursive_binding, names, types, child, child, multiplicities),
        "if": st.builds(SIf, child, child, child),
        "annotation": st.builds(SAnnotation, child, types),
        "type_lambda": st.builds(STypeAbstraction, names, kinds, child),
    }


@st.composite
def nested_terms(draw: st.DrawFn, child: st.SearchStrategy[STerm]) -> STerm:
    return draw(st.one_of(*compound_terms(child).values()))


terms = st.recursive(leaves, nested_terms, max_leaves=10)
# Exercise every outer constructor even in the small deterministic CI profile.
term_cases = {"leaf": leaves, **compound_terms(terms)}
widths = st.sampled_from([20, 40, 120])


def structure(value: Any) -> Any:
    """Ignore spans and name-resolution IDs, which are not represented in source.

    Unlike dataclass equality, compare annotation types too. Include the Python
    value type so bool/int/float confusion cannot pass, and preserve signed zero.
    """
    if isinstance(value, Name):
        return Name, value.name
    if is_dataclass(value):
        return type(value), tuple((f.name, structure(getattr(value, f.name))) for f in fields(value) if f.name != "loc")
    if isinstance(value, (list, tuple)):
        return type(value), tuple(structure(item) for item in value)
    if isinstance(value, float):
        return float, value.hex()
    return type(value), value


def assert_term_roundtrip(term: STerm, width: int) -> None:
    # depth=1 retains expression syntax (let ... in), without display-only
    # normalization or converting a chain of lets into top-level definitions.
    source = sterm_pretty(term, depth=1).best(width, 0).layout(0)
    parsed = parse_expression(source)
    assert structure(parsed) == structure(term), source
    assert sterm_pretty(parsed, depth=1).best(width, 0).layout(0) == source


@pytest.mark.parametrize("case", term_cases)
@given(data=st.data(), width=widths)
def test_term_ast_roundtrip(case: str, data: Any, width: int) -> None:
    term = data.draw(term_cases[case], label="AST")
    note(sterm_pretty(term, depth=1).best(width, 0).layout(0))
    assert_term_roundtrip(term, width)


@given(ty=types, width=widths)
def test_type_ast_roundtrip(ty: SType, width: int) -> None:
    source = stype_pretty(ty).best(width, 0).layout(0)
    note(source)
    parsed = parse_type(source)
    assert structure(parsed) == structure(ty)
    assert pretty_print_stype(parsed) == pretty_print_stype(ty)


@given(term=terms)
def test_public_term_printer_stability(term: STerm) -> None:
    # The public convenience API deliberately beta-reduces, folds constant
    # conditionals, renames unused binders and aligns refined binder names.
    # Check its output is parseable and stable; the raw printer property above
    # checks fidelity to the original AST independently of these rewrites.
    source = pretty_print_sterm(term, top_level=False)
    note(source)
    assert pretty_print_sterm(parse_expression(source), top_level=False) == source


x = SVar(Name("x"))
y = SVar(Name("y"))
z = SVar(Name("z"))


@pytest.mark.parametrize(
    "term",
    [
        SLiteral(False, st_bool),
        SLiteral('"\\\n\t\0😀', st_string),
        SApplication(x, SLiteral(-0.0, st_float)),
        SBy(("assumption", "split")),
        SApplication(x, SBy(("constructor",))),
        SAnnotation(x, st_int),
        SAnnotation(SAbstraction(Name("x"), x), st_int),
        SAnnotation(SLiteral(0, st_int), STypeConstructor(Name("List"), [st_int])),
        SLet(Name("x"), y, x, multiplicity=Multiplicity.M1),
        SRec(Name("x"), st_int, y, x, multiplicity=Multiplicity.M0),
        SRec(Name("x"), SRefinedType(Name("x"), st_int, x), y, x),
        binary("&&", binary("&&", x, y), z),
        binary("||", binary("||", x, y), z),
        binary("<", x, binary("<", y, z)),
        binary("==", binary("==", x, y), z),
        binary("<", binary("==", x, y), z),
    ],
)
def test_shrunk_term_regressions(term: STerm) -> None:
    """Keep discovered counterexamples even when a generated campaign changes."""
    assert_term_roundtrip(term, 20)


def test_nested_type_constructor_regression() -> None:
    ty = STypeConstructor(Name("List"), [STypeConstructor(Name("List"), [st_int])])
    assert structure(parse_type(pretty_print_stype(ty))) == structure(ty)
