"""FIX, TABS and ABS, with a decreasing recursive hypothesis."""

from aeon.synthesis.grammar.nonterminals import grammar_bindings
from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar, liquid_free_vars
from aeon.core.liquid_ops import mk_liquid_and
from aeon.core.substitutions import substitution_in_type, substitution_in_liquid, liquefy
from aeon.core.terms import (
    Abstraction,
    TypeAbstraction,
    RefinementAbstraction,
    Rec,
    Var,
    Application,
    TypeApplication,
    Annotation,
)
from aeon.core.types import (
    AbstractionType,
    TypePolymorphism,
    RefinementPolymorphism,
    TypeConstructor,
    RefinedType,
    TypeVar,
    t_int,
    extract_parts,
)
from aeon.synthesis.modules.synquid.constraints import fresh_name
from aeon.synthesis.modules.synquid.round_trip import erase
from aeon.utils.name import Name
from aeon.verification.constructor_registry import get_measures


def enclosing_function(ctx, name, goal):
    """Recover a declaration schema for a hole occupying its entire body."""
    from aeon.synthesis.modules.synquid.round_trip import match_result
    from aeon.core.instantiation import type_substitution

    schema = ctx.type_of(name)
    if schema is None:
        return None
    parameters = []
    inner = schema
    while isinstance(inner, TypePolymorphism):
        parameters.append(inner.name)
        inner = inner.body
    result = inner
    while isinstance(result, AbstractionType):
        result = result.type
    shapes = match_result(result, goal, set(parameters))
    if shapes is None:
        return None
    instances = []
    for parameter in parameters:
        instance = shapes.get(parameter)
        if instance is None:
            same_name = next((n for n, _ in reversed(ctx.typevars()) if n.name == parameter.name), None)
            if same_name is None:
                return None
            instance = TypeVar(same_name)
        instances.append(instance)
        inner = type_substitution(inner, parameter, instance)
    args = []
    while isinstance(inner, AbstractionType):
        actual = next((n for n, _ in reversed(grammar_bindings(ctx)) if n.name == inner.var_name.name), None)
        if actual is None:
            return None
        args.append(Var(actual))
        inner = substitution_in_type(inner.type, Var(actual), inner.var_name)
    if inner != goal or not args:
        return None

    def close(term):
        term = Annotation(term, schema)
        for instance in instances:
            term = TypeApplication(term, instance)
        for arg in args:
            term = Application(term, arg)
        return term

    return schema, close


def metrics(ctx, params):
    """Each scalar Int metric supplies the well-founded nonnegative order.

    A datatype's declared Int measures are eligible; recursive calls must prove
    nonnegativity as well as strict decrease. No measure is assumed positive.
    """
    for index, (name, ty) in enumerate(params):
        ty = erase(ty)
        if ty == t_int:
            yield index, Var(name)
        elif isinstance(ty, TypeConstructor):
            measures = get_measures(ty.name.name)
            measures.sort(key=lambda s: (not s.endswith("structuralRank"), not s.endswith("size"), s))
            for measure in measures:
                found = next(((n, t) for n, t in ctx.vars() if n.name == measure), None)
                if found is None:
                    continue
                n, mt = found
                term = Var(n)
                args = iter(ty.args)
                while isinstance(mt, TypePolymorphism):
                    arg = next(args, None)
                    if arg is None:
                        break
                    term = TypeApplication(term, arg)
                    mt = mt.body
                if isinstance(mt, AbstractionType) and erase(mt.type) == t_int:
                    yield index, Application(term, Var(name))
                    break


def weaken(schema, ordered_metrics, *, entry_metrics=None):
    """Use the paper's lexicographic order on all eligible arguments.

    Place the tuple obligation on the final measured argument, where all
    preceding callee arguments are in scope. Fresh binders keep caller metrics
    distinct from callee metrics, including dependent parameter refinements.
    """
    from aeon.typechecking.termination import _lexicographic_less

    entries = [liquefy(metric) for _, metric in ordered_metrics]
    assert all(entry is not None for entry in entries)
    caller = entries if entry_metrics is None else [liquefy(metric) for metric in entry_metrics]
    assert all(entry is not None for entry in caller)
    last = ordered_metrics[-1][0]

    def build(ty, index, mapping):
        if isinstance(ty, TypePolymorphism):
            return TypePolymorphism(ty.name, ty.kind, build(ty.body, index, mapping))
        if isinstance(ty, RefinementPolymorphism):
            return RefinementPolymorphism(ty.name, ty.sort, build(ty.body, index, mapping))
        if not isinstance(ty, AbstractionType):
            return ty
        n = fresh_name("recursive_arg")
        domain = ty.var_type
        for original, replacement in mapping.items():
            domain = substitution_in_type(domain, Var(replacement), original)
        replacements = {**mapping, ty.var_name: n}
        if index == last:
            v, base, predicate = extract_parts(domain)
            calls = list(entries)
            for original, replacement in replacements.items():
                calls = [
                    substitution_in_liquid(call, LiquidVar(v if replacement == n else replacement), original)
                    for call in calls
                ]
            condition = _lexicographic_less(calls, caller)
            for call in calls:
                condition = mk_liquid_and(LiquidApp(Name(">=", 0), [call, LiquidLiteralInt(0)]), condition)
            domain = RefinedType(v, base, mk_liquid_and(predicate, condition))
        body = build(ty.type, index + 1, replacements)
        if not isinstance(ty.type, AbstractionType):
            for original, replacement in replacements.items():
                body = substitution_in_type(body, Var(replacement), original)
        return AbstractionType(n, domain, body, multiplicity=ty.multiplicity)

    return build(schema, 0, {})


def recursive_context(ctx, program, name):
    """Constrain source-level recursive calls before expanding applications.

    The hole context otherwise contains the full declared recursive contract.
    Reuse the source's actual termination metric, including for mutual calls,
    so no whole-program recheck is needed to establish decreasing calls.
    """
    from aeon.synthesis.identification import iterate_top_level
    from aeon.typechecking.termination import _align_polymorphic_schema, peel_abstractions
    from aeon.typechecking.typeinfer import _erase_return_refinement
    from aeon.core.types import top
    from aeon.typechecking.context import VariableBinder
    from dataclasses import replace

    def replace_binding(context, target, hypothesis):
        return replace(
            context,
            entries=[
                VariableBinder(target, hypothesis) if getattr(entry, "name", None) == target else entry
                for entry in context.entries
            ],
        )

    owner = next((r for r in iterate_top_level(program) if r.var_name == name), None)
    if owner is None:
        schema = ctx.type_of(name)
        return replace_binding(ctx, name, _erase_return_refinement(schema)) if schema is not None else ctx

    def aligned(schema, value):
        formals, _ = peel_abstractions(value)
        names = iter(formals)

        def rename(ty):
            if isinstance(ty, TypePolymorphism):
                return TypePolymorphism(ty.name, ty.kind, rename(ty.body))
            if isinstance(ty, RefinementPolymorphism):
                return RefinementPolymorphism(ty.name, ty.sort, rename(ty.body))
            if isinstance(ty, AbstractionType):
                n = next(names)
                return AbstractionType(
                    n,
                    ty.var_type,
                    rename(substitution_in_type(ty.type, Var(n), ty.var_name)),
                    multiplicity=ty.multiplicity,
                )
            return ty

        return rename(_align_polymorphic_schema(schema, value)), formals

    family = [(owner.var_name, owner.var_type, owner.var_value, owner.decreasing_by)]
    family.extend((c.name, c.type, c.value, c.decreasing_by) for c in owner.companions)
    for target, schema, value, measures in family:
        if not owner.decreasing_by:
            hypothesis = _erase_return_refinement(schema)
        elif not measures or len(measures) != len(owner.decreasing_by):
            hypothesis = top
        else:
            schema, formals = aligned(schema, value)
            inner = schema
            while isinstance(inner, (TypePolymorphism, RefinementPolymorphism)):
                inner = inner.body
            domains = []
            while isinstance(inner, AbstractionType):
                domains.append(inner.var_type)
                inner = inner.type
            # A higher-order final parameter cannot carry a scalar refinement.
            # Attach the obligation where all metric arguments are in scope.
            position = next(
                (i for i in reversed(range(len(domains))) if isinstance(erase(domains[i]), (TypeConstructor, TypeVar))),
                None,
            )
            metric_variables = {n for metric in measures for n in liquid_free_vars(liquefy(metric))}
            if position is None or any(n in metric_variables for n in formals[position + 1 :]):
                hypothesis = top
            else:
                hypothesis = weaken(
                    schema, [(position, metric) for metric in measures], entry_metrics=owner.decreasing_by
                )
        ctx = replace_binding(ctx, target, hypothesis)
    return ctx


def function_terms(ctx, level, goal, skip, mem, state):
    from aeon.synthesis.modules.synquid.engine import synthes_memory, _local_check

    inner = goal
    prefix = []
    body_ctx = ctx
    branch = state.fork()
    while isinstance(inner, (TypePolymorphism, RefinementPolymorphism)):
        prefix.append(inner)
        if isinstance(inner, TypePolymorphism):
            body_ctx = body_ctx.with_typevar(inner.name, inner.kind)
            branch.context = branch.context.with_typevar(inner.name, inner.kind)
        else:
            body_ctx = body_ctx.with_refinement(inner.name, inner.sort)
            branch.context = branch.context.with_refinement(inner.name, inner.sort)
        inner = inner.body
    params = []
    while isinstance(inner, AbstractionType):
        params.append((inner.var_name, inner.var_type))
        body_ctx = body_ctx.with_var(inner.var_name, inner.var_type)
        branch.bind(inner.var_name, inner.var_type)
        inner = inner.type

    def wrap(body):
        for n, _ in reversed(params):
            body = Abstraction(n, body)
        for binder in reversed(prefix):
            body = (
                TypeAbstraction(binder.name, binder.kind, body)
                if isinstance(binder, TypePolymorphism)
                else RefinementAbstraction(binder.name, binder.sort, body)
            )
        return body

    # FIX introduces one hypothesis before synthesis, rather than waiting to
    # reject non-decreasing complete programs at the final verifier.
    choices = list(metrics(body_ctx, params)) if mem.get("synquid_fix", True) else []
    if not choices:
        for body in synthes_memory(body_ctx, level, inner, skip, mem, branch):
            yield wrap(body)
        return
    if choices:
        name = fresh_name("fix")
        hypothesis = weaken(goal, choices)
        recursive_ctx = body_ctx.with_var(name, hypothesis)
        recursive_state = branch.fork(branch.context.with_var(name, hypothesis))
        for body in synthes_memory(
            recursive_ctx, level, inner, lambda n: False if n == name else skip(n), mem, recursive_state
        ):
            from aeon.typechecking.linearity import _find_var_uses

            if not _find_var_uses(body, name):
                yield wrap(body)
                continue
            result = Rec(name, goal, wrap(body), Var(name), decreasing_by=tuple(metric for _, metric in choices))
            if _local_check(ctx, result, goal, state):
                state.stats.recursive_functions += 1
                yield result
