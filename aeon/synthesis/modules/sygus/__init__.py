"""SyGuS-based synthesis backend (issue #49).

Synthesises code for a *valid subset* of Aeon-core synthesis problems by
translating them into a SyGuS problem, solving it with the cvc5 SyGuS
engine (via its Python API), and translating the answer back into
Aeon-core.

The valid subset is holes whose type is a base SMT type (``Int``, ``Bool``,
``Float``) or a refinement ``{v:T | phi}`` over one of those.  SMT-typed
context variables become the inputs of the function to synthesise, their
refinements become preconditions, and ``phi`` (or ``true`` for bare types)
becomes the specification.

Polymorphism, non-native operators, and non-SMT types are out of scope:
the translation then *fails gracefully* (returns ``None``) and the
synthesizer raises ``SynthesisNotSuccessful`` without crashing.
"""

from aeon.synthesis.modules.sygus.synthesizer import SygusSynthesizer

__all__ = ["SygusSynthesizer"]
