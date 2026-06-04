"""Constructor-based shrinking of property counterexamples.

When a property fails, the first random counterexample is usually larger than it
needs to be (a long list, a big integer). Shrinking searches for a *smaller*
input that still falsifies the property and reports that instead, which makes
failures far easier to read.

The shrinker is generic over the datatype constructors discovered in the
program. For a constructor application like ``cons hd tl`` it produces:

- each recursive child of the same type (e.g. the tail ``tl`` of a list, or a
  subtree) — this is the structural reduction that shortens lists / shrinks
  trees toward their base constructor; and
- the term rebuilt with one argument replaced by a shrink of that argument
  (recursively) — e.g. a smaller element value, or a shorter sub-list.

Base literals (``Int``/``Float``/``Bool``/``String``) shrink toward a canonical
small value. Literals are only shrunk for *unrefined* types: shrinking a value
constrained by a refinement could leave the argument's valid domain, so those
are left untouched (their domain is enforced at generation time instead).

Every candidate is re-tested by the caller and kept only if the property still
fails, so shrinking never invents a spurious counterexample.
"""

from __future__ import annotations

from typing import Iterator

from aeon.core.terms import (
    Annotation,
    Application,
    Literal,
    RefinementApplication,
    Term,
    TypeApplication,
    Var,
)
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    Type,
    TypePolymorphism,
    refined_to_unrefined_type,
    t_bool,
    t_float,
    t_int,
    t_string,
)
from aeon.core.substitutions import substitute_vartype
from aeon.synthesis.grammar.grammar_generation import remove_uninterpreted_functions_from_type
from aeon.utils.name import Name

# Maps a (prefixed) constructor name to its polymorphic core type.
ConstructorTypes = dict[str, Type]


def _peel(term: Term) -> Term:
    while isinstance(term, Annotation):
        term = term.expr
    return term


def decompose_constructor(term: Term, constructor_names: set[str]) -> tuple[Name, list[Type], list[Term]] | None:
    """If ``term`` is a data-constructor application, return
    ``(constructor_name, type_arguments, value_arguments)``; otherwise ``None``.

    Handles the shape produced by generation:
    ``App(App(TypeApp(Var(cons), τ), a1), a2)`` — a ``Var`` head wrapped in
    type/refinement applications, then applied to the value arguments."""
    t = _peel(term)
    args: list[Term] = []
    while isinstance(t, Application):
        args.append(t.arg)
        t = _peel(t.fun)
    args.reverse()

    type_args: list[Type] = []
    while isinstance(t, (TypeApplication, RefinementApplication)):
        if isinstance(t, TypeApplication):
            type_args.insert(0, t.type)
        t = _peel(t.body)

    if isinstance(t, Var) and t.name.name in constructor_names:
        return t.name, type_args, args
    return None


def constructor_signature(cons_type: Type, type_args: list[Type]) -> tuple[list[Type], Type]:
    """Return ``(argument_types, return_type)`` for a constructor instantiated at
    ``type_args``. The abstract refinement (``forall <p:a->Bool>`` and the
    ``{v:a | p v}`` element predicate) is stripped first via
    ``remove_uninterpreted_functions_from_type`` — the same cleaning the grammar
    applies — so the remaining type is a plain polymorphic function."""
    ty = remove_uninterpreted_functions_from_type(cons_type)
    i = 0
    while isinstance(ty, TypePolymorphism):
        if i < len(type_args):
            ty = substitute_vartype(ty.body, type_args[i], ty.name)
        else:
            ty = ty.body
        i += 1
    arg_types: list[Type] = []
    while isinstance(ty, AbstractionType):
        arg_types.append(ty.var_type)
        ty = ty.type
    return arg_types, ty


def _rebuild(cons_name: Name, type_args: list[Type], args: list[Term]) -> Term:
    head: Term = Var(cons_name)
    for ta in type_args:
        head = TypeApplication(head, ta)
    for a in args:
        head = Application(head, a)
    return head


def _same_type(a: Type, b: Type) -> bool:
    return refined_to_unrefined_type(a) == refined_to_unrefined_type(b)


def _shrink_literal(term: Term, ty: Type) -> Iterator[Term]:
    """Shrink a base literal toward a small canonical value. Skipped for refined
    types, whose domain must be preserved."""
    if not isinstance(term, Literal):
        return
    if isinstance(ty, RefinedType):
        return  # do not leave the refinement's valid domain
    value = term.value
    if term.type == t_int and isinstance(value, int):
        # Candidates must strictly decrease in magnitude so shrinking always
        # moves toward zero and terminates (no 0<->1 oscillation).
        seen: set[int] = set()
        for icand in (0, value // 2, value - (1 if value > 0 else -1)):
            if abs(icand) < abs(value) and icand not in seen:
                seen.add(icand)
                yield Literal(icand, t_int)
    elif term.type == t_float and isinstance(value, float):
        for fcand in (0.0, value / 2.0):
            if abs(fcand) < abs(value):
                yield Literal(fcand, t_float)
    elif term.type == t_bool and value is True:
        yield Literal(False, t_bool)
    elif term.type == t_string and isinstance(value, str) and value:
        yield Literal("", t_string)
        if len(value) > 1:
            yield Literal(value[: len(value) // 2], t_string)


def shrinks(
    term: Term,
    ty: Type,
    constructor_types: ConstructorTypes,
    constructor_names: set[str],
) -> Iterator[Term]:
    """Yield candidate terms that are structurally smaller than ``term`` and of
    the same type. Ordered most-impactful-first (whole-term reductions before
    argument shrinks) so greedy minimization converges quickly."""
    decomp = decompose_constructor(term, constructor_names)
    if decomp is None:
        yield from _shrink_literal(term, ty)
        return

    cons_name, type_args, args = decomp
    cons_type = constructor_types.get(cons_name.name)
    if cons_type is None:
        return
    arg_types, _ = constructor_signature(cons_type, type_args)
    if len(arg_types) != len(args):
        return

    # 1) Replace the whole term with any same-typed recursive child (e.g. a
    #    list's tail) — the structural reduction toward the base constructor.
    for arg, at in zip(args, arg_types):
        if _same_type(at, ty):
            yield arg

    # 2) Shrink each argument in place and rebuild.
    for i, (arg, at) in enumerate(zip(args, arg_types)):
        for smaller in shrinks(arg, at, constructor_types, constructor_names):
            yield _rebuild(cons_name, type_args, args[:i] + [smaller] + args[i + 1 :])


def minimize(
    terms: list[Term],
    arg_types: list[Type],
    shrinkable: list[bool],
    still_fails,
    constructor_types: ConstructorTypes,
    constructor_names: set[str],
    max_steps: int = 300,
) -> list[Term]:
    """Greedily shrink a failing argument tuple while the property keeps failing.

    ``still_fails(candidate_terms) -> bool`` re-runs the property; a candidate is
    accepted only when it returns ``True``, so soundness never depends on the
    shrinks themselves being valid. ``shrinkable[i]`` is ``False`` for arguments
    another argument depends on (shrinking them could break the dependency).
    ``max_steps`` bounds the number of property evaluations."""
    current = list(terms)
    steps = 0
    improved = True
    while improved and steps < max_steps:
        improved = False
        for i in range(len(current)):
            if not shrinkable[i]:
                continue
            for cand in shrinks(current[i], arg_types[i], constructor_types, constructor_names):
                steps += 1
                if steps > max_steps:
                    break
                trial = current[:i] + [cand] + current[i + 1 :]
                if still_fails(trial):
                    current = trial
                    improved = True
                    break
            if improved:
                break
    return current
