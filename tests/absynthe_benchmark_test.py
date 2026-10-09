"""Coverage for the portable Absynthe SyGuS string benchmark suite (#561)."""

from __future__ import annotations

from pathlib import Path

import pytest

from aeon.synthesis.benchmarks.absynthe import (
    Sort,
    SygusError,
    evaluate,
    infer_sort,
    load_benchmark,
    parse_benchmark,
    parse_expression,
)


SUITE = Path(__file__).parent.parent / "examples" / "synthesis" / "absynthe"


def expression(source: str):
    result = parse_expression(source)
    infer_sort(result, {"name": Sort.STRING, "firstname": Sort.STRING, "lastname": Sort.STRING})
    return result


@pytest.mark.parametrize(
    ("source", "expected"),
    [
        ('(str.++ "a" "b")', "ab"),
        ('(str.replace "aba" "a" "x")', "xba"),
        ('(str.substr "abc" 1 8)', "bc"),
        ('(str.substr "abc" -1 2)', ""),
        ('(str.at "abc" 1)', "b"),
        ('(str.at "abc" 5)', ""),
        ("(int.to.str 42)", "42"),
        ("(int.to.str -1)", ""),
        ("(+ 2 3)", 5),
        ("(- 2 3)", -1),
        ('(str.len "abc")', 3),
        ('(str.to.int "0042")', 42),
        ('(str.to.int "forty-two")', -1),
        ('(str.indexof "abcabc" "bc" 2)', 4),
        ('(str.indexof "abc" "z" 0)', -1),
        ('(str.prefixof "ab" "abc")', True),
        ('(str.suffixof "bc" "abc")', True),
        ('(str.contains "b" "abc")', True),
        ('(ite (str.contains "a" name) "yes" "no")', "yes"),
    ],
)
def test_interpreter_covers_absynthe_dsl(source: str, expected):
    assert evaluate(expression(source), {"name": "abc", "firstname": "Ada", "lastname": "Lovelace"}) == expected


def test_typechecker_rejects_bad_operator_arguments():
    candidate = parse_expression('(str.substr "text" "zero" 1)')
    with pytest.raises(SygusError, match="expects"):
        infer_sort(candidate, {})


def test_parser_handles_conditional_grammar_comments_and_escaped_strings():
    benchmark = parse_benchmark(
        """; leading comment
        (synth-fun f ((x String)) String
          ((Start String ((ite condition x "a\\\"b")))
           (condition Bool (true false))))
        (constraint (= (f "input") "output"))
        (check-synth)
        """
    )
    assert benchmark.parameters == (("x", Sort.STRING),)
    assert benchmark.grammar[0].name == "Start"
    assert benchmark.constraints[0].inputs == ("input",)
    assert benchmark.constraints[0].expected == "output"


REFERENCES = {
    "bikes.sl": "(str.substr name 0 (- (str.len name) 3))",
    "phone.sl": '(str.substr name 0 (str.indexof name "-" 0))',
    "firstname.sl": '(str.substr name 0 (str.indexof name " " 0))',
    "lastname.sl": '(str.substr name (+ (str.indexof name " " 0) 1) (- (str.len name) (+ (str.indexof name " " 0) 1)))',
    "dr-name.sl": '(str.++ "Dr." (str.++ " " (str.substr name 0 (str.indexof name " " 0))))',
    "name-combine.sl": '(str.++ firstname (str.++ " " lastname))',
    "name-combine-2.sl": '(str.++ firstname (str.++ " " (str.++ (str.at lastname 0) ".")))',
}


@pytest.mark.parametrize("filename", sorted(REFERENCES))
def test_ported_benchmarks_parse_and_reference_programs_are_exact(filename: str):
    benchmark = load_benchmark(SUITE / filename)
    candidate = parse_expression(REFERENCES[filename])
    assert benchmark.fitness(candidate) == 0
    assert benchmark.satisfies(candidate)
    assert {rule.sort for rule in benchmark.grammar} == {Sort.STRING, Sort.INT, Sort.BOOL}


def test_fitness_reports_the_number_of_violated_constraints():
    benchmark = load_benchmark(SUITE / "bikes.sl")
    wrong = parse_expression('"Ducati"')
    assert benchmark.fitness(wrong) == 3
    assert len(benchmark.violated_constraints(wrong)) == 3


def test_invalid_candidate_has_maximum_violation_score():
    benchmark = load_benchmark(SUITE / "bikes.sl")
    ill_typed = parse_expression("0")
    assert benchmark.fitness(ill_typed) == len(benchmark.constraints)
