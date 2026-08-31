from __future__ import annotations

import aeon


def test_public_api_parses_checks_and_runs():
    program = aeon.parse("def answer : Int := 42;", no_main=True)
    assert program.check() == []
    # ``no_main`` evaluates the elaborated program tail, whose convention is
    # the unit value represented by the interpreter as ``1``.
    assert program.run() == 1


def test_public_api_returns_check_errors_without_exposing_core_modules():
    errors = aeon.check("def answer : Int := true;", no_main=True)
    assert errors
    assert set(aeon.__all__) == {"Program", "parse", "check", "synthesize"}


def test_public_api_drives_native_synthesis():
    program = aeon.synthesize("def answer : Int := ?hole;", backend="gp", budget=1, no_main=True)
    assert program.check() == []


def test_implementation_packages_do_not_publish_python_names():
    import aeon.compilation
    import aeon.elaboration
    import aeon.optimization

    assert aeon.compilation.__all__ == []
    assert aeon.elaboration.__all__ == []
    assert aeon.optimization.__all__ == []

    import aeon.synthesis
    import aeon.synthesis.modules.afta
    import aeon.synthesis.modules.cata
    import aeon.synthesis.modules.contata
    import aeon.synthesis.modules.fta
    import aeon.synthesis.modules.lta
    import aeon.synthesis.modules.sygus
    import aeon.synthesis.modules.symetric

    assert aeon.synthesis.__all__ == []
    assert aeon.synthesis.modules.afta.__all__ == []
    assert aeon.synthesis.modules.cata.__all__ == []
    assert aeon.synthesis.modules.contata.__all__ == []
    assert aeon.synthesis.modules.fta.__all__ == []
    assert aeon.synthesis.modules.lta.__all__ == []
    assert aeon.synthesis.modules.sygus.__all__ == []
    assert aeon.synthesis.modules.symetric.__all__ == []
