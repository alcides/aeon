"""Imported datatypes and shared dependencies retain concrete identities."""

import pytest

from aeon.compilation.compile import compile_file
from aeon.compilation.session import CompilationSession
from aeon.core.types import AbstractionType, TypeConstructor
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


@pytest.fixture
def libraries(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    (tmp_path / "Shared.ae").write_text("""
    inductive Shared | mk (value:Int) : Shared
    def value(s:Shared):Int := match s with | Shared.mk n => n;
    def twice(n:Int):Int := n * 2;
    """)
    (tmp_path / "Consumer.ae").write_text("""
    import Shared;
    def identity(s:Shared):Shared := s;
    def value(s:Shared):Int := Shared.twice (Shared.value (identity s));
    """)
    (tmp_path / "Other.ae").write_text("""
    import Shared;
    def increment(n:Int):Int := Shared.twice n + 1;
    """)
    return tmp_path


def test_imported_datatype_is_not_implicitly_quantified(libraries):
    with CompilationSession().activate():
        unit, errors = compile_file(str(libraries / "Consumer.ae"), is_main=False, use_cache=False)
    assert not errors
    ty = unit.exports["identity"].core_type
    assert isinstance(ty, AbstractionType)
    assert isinstance(ty.var_type, TypeConstructor)
    assert isinstance(ty.type, TypeConstructor)
    assert ty.var_type.name.name == ty.type.name.name == "Shared"


@pytest.mark.parametrize(
    "imports",
    [
        "import Consumer; import Shared; import Other;",
        "import Other; import Shared; import Consumer;",
        "import Consumer; import Other;",
    ],
)
def test_shared_dependencies_precede_every_consumer(libraries, imports):
    driver = AeonDriver(AeonConfig("gp", SilentSynthesisUI(), 0))
    errors = list(
        driver.parse(aeon_code=imports + "def main(args:Int):Int := Consumer.value (Shared.mk 20) + Other.increment 1;")
    )
    assert not errors, "\n".join(map(str, errors))
    assert driver.run() == 43
