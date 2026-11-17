"""Resugared eliminators must remain executable, scoped Aeon expressions."""

import pytest

from aeon.core.terms import Abstraction
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.sugar.lifting import lift
from aeon.sugar.parser import parse_expression, parse_program
from aeon.synthesis.identification import iterate_top_level
from aeon.synthesis.uis.api import SilentSynthesisUI, SynthesisUI
from aeon.utils.name import Name
from aeon.utils.pprint import pretty_print_node, pretty_print_sterm


CANDIDATE = """
inductive Candidate
| first (value:Int) : Candidate
| second : Candidate
"""


def compile_source(source):
    driver = AeonDriver(AeonConfig("tdsyn", SilentSynthesisUI(), 5, no_main=True))
    assert not driver.parse(aeon_code=source)
    return driver


def function_body(driver, name="f"):
    term = next(d.var_value for d in iterate_top_level(driver.core) if d.var_name.name == name)
    while isinstance(term, Abstraction):
        term = term.body
    return term


def exported(driver, name="f"):
    namespace = {}
    exec(driver.export(name), namespace)
    return namespace[name]


def round_trip(body, *, prefix=CANDIDATE, signature="(c:Candidate):Int"):
    original = compile_source(f"{prefix}\ndef f {signature} := {body};")
    with original.session.activate():
        printed = pretty_print_sterm(lift(function_body(original)), top_level=False)
    reparsed = compile_source(f"{prefix}\ndef f {signature} := {printed};")
    return printed, exported(original), exported(reparsed)


@pytest.mark.parametrize(
    "body",
    [
        "Candidate_rec{Int} c (fun ignored => 0) 1",
        "match c with | first ignored => 0 | second => 1",
    ],
)
def test_direct_and_lowered_eliminators_print_as_matches(body):
    printed, before, after = round_trip(body)
    assert "Candidate_rec" not in printed
    assert "match c with" in printed
    assert "| Candidate.first _ => 0" in printed
    assert "| Candidate.second => 1" in printed
    for value in [("Candidate_first", 42), ("Candidate_first", -7), ("Candidate_second",)]:
        assert before(value) == after(value)


@pytest.mark.parametrize(
    "body",
    [
        "let tag := Candidate_rec{Int} c (fun n => n) 1 in tag + 3",
        "10 + Candidate_rec{Int} c (fun n => n) 1",
        "((fun x => x + 2):(x:Int)->Int) (Candidate_rec{Int} c (fun n => n) 1)",
        "if (Candidate_rec{Int} c (fun n => n) 1) > 0 then 8 else 9",
        "Candidate_rec{Int} c (fun n => Candidate_rec{Int} c (fun m => n + m) 7) 2",
    ],
)
def test_matches_round_trip_in_expression_contexts(body):
    printed, before, after = round_trip(body)
    assert "Candidate_rec" not in printed
    for value in [("Candidate_first", 4), ("Candidate_first", -1), ("Candidate_second",)]:
        assert before(value) == after(value)


def test_named_handlers_are_eta_expanded_without_capturing_names():
    prefix = CANDIDATE + "def field:Int := 10; def add (n:Int):Int := n + field;"
    printed, before, after = round_trip("Candidate_rec{Int} c add field", prefix=prefix)
    assert "Candidate_rec" not in printed
    assert "Candidate.first field_" in printed
    assert before(("Candidate_first", 5)) == after(("Candidate_first", 5)) == 15
    assert before(("Candidate_second",)) == after(("Candidate_second",)) == 10


def test_computed_handlers_keep_eager_evaluation_order(capsys):
    prefix = (
        CANDIDATE
        + """
        def make (n:Int):Candidate := native "(print(n), ('Candidate_second',))[1]";
        def mark (n:Int):Int := native "(print(n), n)[1]";
        def handler (n:Int):(x:Int)->Int := let saved := mark n in fun x => x + saved;
    """
    )
    printed, before, after = round_trip("Candidate_rec{Int} (make 1) (handler 2) (mark 3)", prefix=prefix)
    assert "match_handler" in printed
    assert "Candidate_rec" not in printed
    capsys.readouterr()
    assert before(("Candidate_first", 0)) == 3
    original_output = capsys.readouterr().out
    assert after(("Candidate_first", 0)) == 3
    assert capsys.readouterr().out == original_output == "1\n2\n3\n"


def test_parametric_recursor():
    prefix = """
        inductive Maybe a
        | none : (Maybe a)
        | some (value:a) : (Maybe a)
    """
    printed, before, after = round_trip(
        "Maybe_rec{Int}{Int} m 0 (fun x => x)", prefix=prefix, signature="(m:(Maybe Int)):Int"
    )
    assert "Maybe_rec" not in printed
    assert "Maybe.some x" in printed
    assert before(("Maybe_some", 19)) == after(("Maybe_some", 19)) == 19


def test_predicate_polymorphic_recursor():
    prefix = """
        inductive Pair forall <r:Int -> Int -> Bool>
        | pair (x:Int) (y:{v:Int | r x v}):Pair{|r|}
    """
    printed, before, after = round_trip(
        "Pair_rec{Int}{|fun x => fun y => x < y|} p (fun x => fun y => y - x)",
        prefix=prefix,
        signature="(p:Pair{|fun x => fun y => x < y|}):Int",
    )
    assert "Pair_rec" not in printed
    assert "Pair.pair x y" in printed
    assert before(("Pair_pair", 2, 9)) == after(("Pair_pair", 2, 9)) == 7


def test_unrelated_and_shadowing_functions_are_not_matches():
    prefix = CANDIDATE + "def other_rec (n:Int):Int := n+1;"
    driver = compile_source(prefix + "def f (Candidate_rec:(x:Int)->Int):Int := Candidate_rec (other_rec 2);")
    with driver.session.activate():
        printed = pretty_print_sterm(lift(function_body(driver)), top_level=False)
    assert "match" not in printed
    assert "Candidate_rec" in printed and "other_rec" in printed


def test_partial_eliminator_remains_a_function_application():
    driver = compile_source(
        CANDIDATE + "def f(c:Candidate):(h:(x:Int)->Int)->(other:Int)->Int := Candidate_rec{Int} c;"
    )
    with driver.session.activate():
        printed = pretty_print_sterm(lift(function_body(driver)), top_level=False)
    assert "match" not in printed
    assert "Candidate_rec" in printed


def test_independent_compilation_sessions_do_not_reinterpret_old_names():
    first = compile_source(CANDIDATE + "def f(c:Candidate):Int := Candidate_rec{Int} c (fun _ => 0) 1;")
    term = lift(function_body(first))
    second = compile_source("def Candidate_rec(n:Int):Int := n; def f(n:Int):Int := Candidate_rec n;")
    with second.session.activate():
        assert "match" not in pretty_print_sterm(term, top_level=False)
    with first.session.activate():
        assert "match" in pretty_print_sterm(term, top_level=False)


def test_whole_program_recovers_schema_without_active_compilation_session():
    driver = compile_source(CANDIDATE + "def f(c:Candidate):Int := Candidate_rec{Int} c (fun _ => 0) 1;")
    printed = pretty_print_sterm(lift(driver.core))
    assert "match c with" in printed


def test_source_matches_preserve_outer_variables_and_open_pattern_binders():
    text = "fun c => match c with | first n => ?h | second => 1"
    printed = pretty_print_sterm(parse_expression(text), top_level=False)
    assert "fun c" in printed and "first n" in printed
    parse_expression(printed)


def test_source_formatter_handles_nested_matches():
    source = (
        CANDIDATE
        + """
        def f(c:Candidate):Int := match c with
        | first n => (match c with | first m => n + m | second => 2)
        | second => 1;
    """
    )
    printed = pretty_print_node(parse_program(source))
    assert "?" not in printed
    assert exported(compile_source(printed))(("Candidate_first", 4)) == 8


def test_synthesis_display_prints_local_lets_as_expressions(capsys):
    driver = compile_source(
        CANDIDATE + "def f(c:Candidate):Int := let tag := Candidate_rec{Int} c (fun _ => 0) 1 in tag;"
    )
    with driver.session.activate():
        SynthesisUI().display_results(driver.core, {Name("hole", 0): lift(function_body(driver))})
    output = capsys.readouterr().out
    assert "let tag :=" in output and "match c with" in output
    assert "def tag" not in output


def test_imported_eliminators_from_cached_modules(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    (tmp_path / "Candidate.ae").write_text(CANDIDATE)
    source = (
        "import Candidate\ndef f(c:Candidate):Int := match c with | Candidate.first n => n | Candidate.second => 1;"
    )
    # The second compilation can load the module's .aec file in a new session.
    for _ in range(2):
        driver = compile_source(source)
        with driver.session.activate():
            printed = pretty_print_sterm(lift(function_body(driver)), top_level=False)
        assert "Candidate_rec" not in printed
        assert "match c with" in printed
        restored = compile_source(f"import Candidate\ndef f(c:Candidate):Int := {printed};")
        assert exported(restored)(("Candidate_first", 23)) == 23


def test_linear_constructor_fields_keep_their_usage():
    prefix = "inductive Token | token (1 value:Int):Token"
    printed, before, after = round_trip("Token_rec{Int} c (fun x => x)", prefix=prefix, signature="(c:Token):Int")
    assert "Token.token x" in printed
    assert before(("Token_token", 8)) == after(("Token_token", 8)) == 8


def test_pattern_binder_used_only_in_a_refinement_is_not_discarded():
    prefix = "inductive Pair | pair (left:Int) (right:Int):Pair"
    printed, before, after = round_trip(
        "Pair_rec{Int} c (fun x => fun y => ((y):{v:Int | x = x}))",
        prefix=prefix,
        signature="(c:Pair):Int",
    )
    assert "Pair.pair x y" in printed
    assert before(("Pair_pair", 1, 5)) == after(("Pair_pair", 1, 5)) == 5
