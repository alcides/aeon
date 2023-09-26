from aeon.sugar.parser import parse_program


def test_program_locations():
    k = parse_program("a = 1")
    assert k.source_location.start_line == 0
