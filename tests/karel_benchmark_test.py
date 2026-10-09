"""Regression coverage for the Karel synthesis benchmark port (#564)."""

from aeon.benchmarks.karel import World, generate_examples, parse, run


def test_source_syntax_executes_a_repeat_program():
    source = "DEF run m( REPEAT R=2 r( move r) m)"
    world = World.parse("#####\n#>..#\n#####")
    assert run(source, world).render() == "#####\n#..>#\n#####"


def test_conditionals_markers_and_turns_match_karel_actions():
    source = "DEF run m( IFELSE c( markersPresent c) i( pickMarker i) ELSE e( turnRight e) m)"
    marked = World.parse("#####\n#>..#\n#####").update_markers(1)
    empty = World.parse("#####\n#>..#\n#####")
    assert run(source, marked).render() == "#####\n#>..#\n#####"
    assert run(source, empty).render() == "#####\n#v..#\n#####"


def test_parser_rejects_invalid_programs_and_bounds_loops():
    try:
        parse("DEF run m( teleport m)")
    except ValueError as error:
        assert "unknown" in str(error)
    else:  # pragma: no cover
        raise AssertionError("invalid Karel action accepted")
    looping = "DEF run m( WHILE c( noMarkersPresent c) w( turnLeft w) m)"
    try:
        run(looping, World.parse("#####\n#>..#\n#####"), step_limit=10)
    except RuntimeError as error:
        assert "step limit" in str(error)
    else:  # pragma: no cover
        raise AssertionError("non-terminating program was not bounded")


def test_seeded_examples_are_deterministic_and_executable():
    source = "DEF run m( IF c( frontIsClear c) i( move i) m)"
    first = generate_examples(source, seed=17, count=3)
    second = generate_examples(source, seed=17, count=3)
    assert first == second
    assert all(output == run(source, input) for input, output in first)
