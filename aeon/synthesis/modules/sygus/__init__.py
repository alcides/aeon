"""SyGuS-based synthesis backend (issue #49).

Synthesises code for a *valid subset* of Aeon-core synthesis problems by
translating them into a SyGuS problem, solving it with the cvc5 SyGuS
engine (via its Python API), and translating the answer back into
Aeon-core.

The valid subset is the holes whose type is a refined base type
``{v:T | phi}`` with ``T in {Int, Bool, Float}``.  SMT-typed context
variables become the inputs of the function to synthesise, their
refinements become preconditions, and ``phi`` becomes the specification.

Polymorphism, non-native operators, and non-SMT types are out of scope:
the translation then *fails gracefully* (returns ``None``) and the
synthesizer raises ``SynthesisNotSuccessful`` without crashing.
"""

from aeon.synthesis.modules.sygus.synthesizer import SygusSynthesizer

__all__ = ["SygusSynthesizer"]
