"""Finite, sorted qualifier templates and executable guard realizations."""

from itertools import product

from aeon.core.liquid import LiquidApp, LiquidVar, LiquidLiteralBool
from aeon.core.substitutions import substitution_in_liquid, liquefy
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    TypeConstructor,
    TypeVar,
    TypePolymorphism,
    RefinementPolymorphism,
    t_bool,
)
from aeon.core.terms import Var, Literal, Application, Annotation
from aeon.typechecking.liquid import lower_context, check_liquid, LiquidTypeCheckException
from aeon.typechecking.qualifiers import extract_qualifier_atoms
from aeon.synthesis.modules.synquid.guards import bool_terms_from_qualifier_atoms
from aeon.utils.name import Name


def base(ty):
    return base(ty.type) if isinstance(ty, RefinedType) else ty


def vocabulary(ctx, goal):
    """Instantiate spec templates in this scope, including Boolean measures.

    The set is finite because placeholders range over current variables. Nested
    Boolean subformulas are also qualifiers (e.g. the RHS of a Boolean result
    equality). Ghost path binders are not program variables.
    """
    atoms = extract_qualifier_atoms(ctx, goal, max_atoms=None)
    sorts = {}

    def collect(ty):
        if isinstance(ty, RefinedType):
            sorts[ty.name] = base(ty)
            collect(ty.type)
        elif isinstance(ty, AbstractionType):
            sorts[ty.var_name] = base(ty.var_type)
            collect(ty.var_type)
            collect(ty.type)
        elif isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
            collect(ty.body)
        elif isinstance(ty, TypeConstructor):
            for arg in ty.args:
                collect(arg)

    for n, ty in ctx.vars():
        sorts[n] = base(ty)
        collect(ty)
    collect(goal)
    visible = {
        n: base(t)
        for n, t in ctx.concrete_vars()
        if not n.name.startswith("_sq_path") and isinstance(base(t), (TypeConstructor, TypeVar))
    }
    lc = lower_context(ctx)
    lc.variables.update(visible)
    templates = set()

    def visit(atom):
        templates.add(atom)
        if isinstance(atom, LiquidApp):
            for arg in atom.args:
                visit(arg)

    for atom in atoms:
        visit(atom)

    def variables(atom):
        if isinstance(atom, LiquidVar):
            return {atom.name}
        if isinstance(atom, LiquidApp):
            return set().union(*(variables(a) for a in atom.args))
        return set()

    out = set()
    for template in templates:
        names = sorted(variables(template), key=str)
        pools = []
        for n in names:
            # Already-scoped names retain their identity; unbound names are
            # typed placeholders from a component/goal signature.
            if n in visible:
                pools.append([LiquidVar(n)])
            else:
                ty = sorts.get(n)
                pools.append([LiquidVar(v) for v, vt in visible.items() if vt == ty or isinstance(ty, TypeVar)])
        for args in product(*pools):
            atom = template
            for n, arg in zip(names, args):
                atom = substitution_in_liquid(atom, arg, n)
            try:
                if atom not in (LiquidLiteralBool(True), LiquidLiteralBool(False)) and check_liquid(lc, atom, t_bool):
                    out.add(atom)
            except (LiquidTypeCheckException, AssertionError, KeyError):
                pass
    # Retain relational placeholder templates, including 0/1 literals.
    for term in bool_terms_from_qualifier_atoms(ctx, atoms, max_terms=None):
        atom = liquefy(term)
        if atom is not None:
            try:
                if check_liquid(lc, atom, t_bool):
                    out.add(atom)
            except LiquidTypeCheckException:
                pass
    return frozenset(out)


def realize(ctx, guard):
    """Cheap executable atoms; other conditions become a synthesis subgoal."""
    if isinstance(guard, LiquidLiteralBool):
        return Literal(guard.value, t_bool)
    if isinstance(guard, LiquidVar) and any(n == guard.name and base(t) == t_bool for n, t in ctx.concrete_vars()):
        return Var(guard.name)
    atoms = bool_terms_from_qualifier_atoms(ctx, frozenset({guard}), max_terms=None)
    for term in atoms:
        if liquefy(term) == guard:
            return term.expr if isinstance(term, Annotation) else term
    if isinstance(guard, LiquidApp) and guard.fun in (Name("&&", 0), Name("||", 0), Name("!", 0)):
        args = [realize(ctx, arg) for arg in guard.args]
        if all(arg is not None for arg in args):
            term = Var(guard.fun)
            for arg in args:
                term = Application(term, arg)
            return term
    return None
