import random

from aeon.core.terms import Var
from aeon.synthesis.modules.symetric.synthesizer import Component, SymetricSynthesizer
from aeon.utils.name import Name


def generator(builders, atoms=None):
    backend = SymetricSynthesizer()
    backend._builders = builders
    backend._atoms = atoms or {}
    return backend


def test_unproductive_direct_recursion_stops():
    backend = generator({"A": [Component(Name("loop", 1), ("A",), "A")]})
    assert backend._gen("A", 5, random.Random(0)) is None


def test_unproductive_mutual_recursion_stops():
    backend = generator({"A": [Component(Name("a", 1), ("B",), "A")], "B": [Component(Name("b", 2), ("A",), "B")]})
    assert backend._gen("A", 5, random.Random(0)) is None


def test_productive_chain_can_reach_atom_at_limit():
    atom = Var(Name("leaf", 3))
    backend = generator({"A": [Component(Name("a", 1), ("B",), "A")]}, {"B": [atom]})
    assert backend._gen("A", 1, random.Random(0)).arg == atom
    assert backend._gen("A", 0, random.Random(0)) is None
