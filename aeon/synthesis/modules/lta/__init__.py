"""Liquid Tree Automata (LTA) for refinement-typed Component-Based Synthesis.

Implements the core ideas of:
  Mishra & Jagannathan, "Liquid Tree Automata", arXiv:2605.13456 (2026).

An LTA is a tree-automaton variant whose alphabet ranges over the symbols of a
refinement-typed lambda-calculus, whose transitions encode well-formedness and
type-derivation rules, and whose constraints support both syntactic (=) and
semantic (entailment, ⊨) atomic predicates over positions.

This module exposes the LTASynthesizer backend, registered as the "lta" synthesizer.
"""

from aeon.synthesis.modules.lta.synthesizer import LTASynthesizer

__all__ = ["LTASynthesizer"]
