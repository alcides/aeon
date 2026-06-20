"""Contata: a genuine Constraint-Annotated Tree Automaton (CATA) version space.

Implements the core of Miltner, Wang, Chaudhuri & Dillig, *Relational Synthesis
of Recursive Programs via Constraint Annotated Tree Automata* (CAV 2024) — as an
actual symbolic version space, rather than the enumerate-each-tree-and-typecheck
approximation of the ``cata`` backend.

The defining idea (paper §4): a candidate body is represented **symbolically** as
a tree over the DSL, where calls to the functions under synthesis are
*uninterpreted functions*. A body therefore has a value that is a *formula* over
those uninterpreted functions — no evaluation, so recursion and mutual recursion
need no fixpoint and there is no circularity. A run is *accepted under a model*
(Def. 6) iff the conjunction of its transition constraints together with the
specification is satisfiable — checked by z3. For a whole ``mutual`` group all
members' bodies and all example inputs are discharged in **one** SMT query, so a
solution is mutually consistent by construction.

See :mod:`aeon.synthesis.modules.contata.cata`.
"""

from aeon.synthesis.modules.contata.cata import synthesize_group, ContataResult

__all__ = ["synthesize_group", "ContataResult"]
