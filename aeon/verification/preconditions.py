"""Check calls in refinements before compile-time evaluation erases them."""

from dataclasses import fields, is_dataclass, replace

from aeon.verification.vcs import LiquidConstraint
from aeon.utils.name import Name

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, liquid_free_vars
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType, RefinedType, TypePolymorphism, RefinementPolymorphism
from aeon.errors import CoreTypeCheckingError
from aeon.sugar.lowering import liquefy, type_to_core, LiquefactionException
from aeon.sugar.program import STerm, SRec, SAbstraction, STypeAbstraction, SRefinementAbstraction, SVar
from aeon.sugar.substitutions import substitution_sterm_in_stype
from aeon.sugar.stypes import SType, SAbstractionType, SRefinedType, STypePolymorphism, SRefinementPolymorphism
from aeon.typechecking.entailment import entailment
from aeon.typechecking.context import TypingContext, VariableBinder, TypeBinder, TypeConstructorBinder
from aeon.verification.sub import lower_constraint_type_keep_refinements


def _goal_context(ctx, goal):
    entries = [entry for entry in ctx.entries if isinstance(entry, (TypeBinder, TypeConstructorBinder))]
    pending = list(liquid_free_vars(goal))
    seen = set()
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        ty = ctx.type_of(name)
        if ty is None:
            continue
        if isinstance(ty, RefinedType):
            pending.extend(v for v in liquid_free_vars(ty.refinement) if v != ty.name)
        elif isinstance(ty, (AbstractionType, TypePolymorphism, RefinementPolymorphism)):
            abstract = set()
            while isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
                if isinstance(ty, RefinementPolymorphism):
                    abstract.add(ty.name)
                ty = ty.body

            def predicate(p):
                if isinstance(p, LiquidApp):
                    return (
                        LiquidLiteralBool(True)
                        if p.fun in abstract
                        else replace(p, args=[predicate(a) for a in p.args])
                    )
                return p

            def instantiated(t):
                if isinstance(t, RefinedType):
                    return replace(t, refinement=predicate(t.refinement))
                if isinstance(t, AbstractionType):
                    return replace(t, var_type=instantiated(t.var_type), type=instantiated(t.type))
                return t

            ty = instantiated(lower_constraint_type_keep_refinements(ty))

        def dependencies(t, bound=frozenset()):
            if isinstance(t, RefinedType):
                pending.extend(v for v in liquid_free_vars(t.refinement) if v not in bound and v != t.name)
            elif isinstance(t, AbstractionType):
                dependencies(t.var_type, bound)
                dependencies(t.type, bound | {t.var_name})

        dependencies(ty)
        entries.append(VariableBinder(name, ty))
    return TypingContext(entries)


class RefinementPreconditionError(CoreTypeCheckingError):
    def __init__(self, function, predicate, loc):
        self.function, self.predicate, self.loc = function, predicate, loc

    def __str__(self):
        return f"Cannot establish precondition {self.predicate} for call to {self.function.name} in refinement."

    def position(self):
        return self.loc


def check_refinement_calls(term: STerm, ctx, *, source_path=None):
    """Check liquid calls in source types without assuming the type being checked.

    Implications and conditionals restrict the context of their right-hand side
    and branches. A result refinement is never evidence for its own calls.
    """

    def calls(expr, local, assumptions=()):
        if not isinstance(expr, LiquidApp):
            return
        if expr.fun.name == "ite" and len(expr.args) == 3:
            cond, yes, no = expr.args
            calls(cond, local, assumptions)
            calls(yes, local, (*assumptions, cond))
            calls(no, local, (*assumptions, LiquidApp(Name("!", 0), [cond])))
            return
        if expr.fun.name in ("-->", "&&") and len(expr.args) == 2:
            left, right = expr.args
            calls(left, local, assumptions)
            calls(right, local, (*assumptions, left))
            return
        for arg in expr.args:
            calls(arg, local, assumptions)
        ty = local.type_of(expr.fun)
        abstract_predicates = set()
        while isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
            if isinstance(ty, RefinementPolymorphism):
                abstract_predicates.add(ty.name)
            ty = ty.body

        def instantiate(predicate):
            if isinstance(predicate, LiquidApp):
                if predicate.fun in abstract_predicates:
                    # Liquid calls omit implicit abstract refinement arguments.
                    # Their inferred instantiations are checked by the core pass.
                    return LiquidLiteralBool(True)
                return LiquidApp(predicate.fun, [instantiate(a) for a in predicate.args], loc=predicate.loc)
            return predicate

        substitutions = []
        for arg in expr.args:
            if not isinstance(ty, AbstractionType):
                break
            if isinstance(ty.var_type, RefinedType):
                pre = substitution_in_liquid(instantiate(ty.var_type.refinement), arg, ty.var_type.name)
                for name, value in substitutions:
                    pre = substitution_in_liquid(pre, value, name)
                if pre != LiquidLiteralBool(True):
                    goal = pre
                    for assumption in reversed(assumptions):
                        goal = LiquidApp(Name("-->", 0), [assumption, goal])
                    unknown = [v for v in liquid_free_vars(goal) if local.type_of(v) is None]
                    if unknown or not entailment(_goal_context(local, goal), LiquidConstraint(goal)):
                        raise RefinementPreconditionError(expr.fun, pre, expr.loc)
            substitutions.append((ty.var_name, arg))
            ty = ty.type

    def representable(ty):
        if isinstance(ty, SRefinedType):
            try:
                predicate = liquefy(ty.refinement)
            except LiquefactionException:
                predicate = None
            return replace(ty, type=representable(ty.type)) if predicate is not None else representable(ty.type)
        if isinstance(ty, SAbstractionType):
            return replace(ty, var_type=representable(ty.var_type), type=representable(ty.type))
        if isinstance(ty, (STypePolymorphism, SRefinementPolymorphism)):
            return replace(ty, body=representable(ty.body))
        return ty

    def surface_calls(node, local):
        try:
            predicate = liquefy(node)
        except LiquefactionException:
            predicate = None
        if predicate is not None:
            calls(predicate, local)
            return
        # Higher-order predicates can contain ordinary first-order calls even
        # when the complete expression cannot be sent to SMT.
        for field in fields(node):
            value = getattr(node, field.name)
            if isinstance(value, STerm):
                surface_calls(value, local)

    def check_type(ty, local):
        if isinstance(ty, SAbstractionType):
            check_type(ty.var_type, local)
            check_type(ty.type, local.with_var(ty.var_name, type_to_core(representable(ty.var_type))))
        elif isinstance(ty, STypePolymorphism):
            check_type(ty.body, local.with_typevar(ty.name, ty.kind))
        elif isinstance(ty, SRefinementPolymorphism):
            check_type(ty.body, local.with_var(ty.name, type_to_core(ty.sort)))
        elif isinstance(ty, SRefinedType):
            check_type(ty.type, local)
            surface_calls(ty.refinement, local.with_var(ty.name, type_to_core(ty.type)))

    needed = {}

    def needs_check(node):
        key = id(node)
        if key not in needed:
            needed[key] = isinstance(node, SRefinedType) or (
                isinstance(node, (STerm, SType))
                and is_dataclass(node)
                and any(
                    needs_check(getattr(node, f.name))
                    for f in fields(node)
                    if isinstance(getattr(node, f.name), (STerm, SType))
                )
            )
        return needed[key]

    def visit(node, local, expected=None):
        if not needs_check(node):
            return
        from aeon.sugar.program import SApplication, SLet, SAnnotation, SIf
        from aeon.sugar.lowering import lower_to_core
        from aeon.sugar.lifting import lift_type
        from aeon.typechecking.typeinfer import synth
        from aeon.core.types import ExistentialType, t_unit
        from aeon.utils.name import fresh_counter

        def open_type(ty, context):
            if isinstance(ty, ExistentialType):
                for name, bound in ty.binders:
                    context = context.with_var(name, bound)
                ty = ty.body
            return ty, context

        if isinstance(node, SAnnotation):
            check_type(node.type, local)
            visit(node.expr, local, node.type)
            return
        if isinstance(node, SLet):
            visit(node.var_value, local)
            _, ty = synth(local, lower_to_core(node.var_value))
            ty, inner = open_type(ty, local)
            visit(node.body, inner.with_var(node.var_name, ty), expected)
            return
        if isinstance(node, SApplication):
            visit(node.fun, local)
            if isinstance(node.arg, SAbstraction):
                _, fun_ty = synth(local, lower_to_core(node.fun))
                fun_ty, inner = open_type(fun_ty, local)
                domain = lift_type(fun_ty.var_type) if isinstance(fun_ty, AbstractionType) else None
                visit(node.arg, inner, domain)
            else:
                visit(node.arg, local)
            return
        if isinstance(node, SIf):
            visit(node.cond, local)
            cond = liquefy(node.cond)
            if cond is None:
                visit(node.then, local, expected)
                visit(node.otherwise, local, expected)
                return
            for body, fact in ((node.then, cond), (node.otherwise, LiquidApp(Name("!", 0), [cond]))):
                name = Name("_guard", fresh_counter.fresh())
                visit(body, local.with_var(name, RefinedType(name, t_unit, fact)), expected)
            return
        if isinstance(node, SAbstraction) and isinstance(expected, SAbstractionType):
            inner = substitution_sterm_in_stype(expected.type, SVar(node.var_name), expected.var_name)
            visit(node.body, local.with_var(node.var_name, type_to_core(representable(expected.var_type))), inner)
            return
        if isinstance(node, STypeAbstraction) and isinstance(expected, STypePolymorphism):
            from aeon.sugar.substitutions import substitute_svartype_in_stype
            from aeon.sugar.stypes import STypeVar

            body_type = substitute_svartype_in_stype(expected.body, STypeVar(node.name), expected.name)
            visit(node.body, local.with_typevar(node.name, node.kind), body_type)
            return
        if isinstance(node, SRefinementAbstraction) and isinstance(expected, SRefinementPolymorphism):
            visit(node.body, local.with_var(node.name, type_to_core(node.sort)), expected.body)
            return
        if isinstance(node, SRec):
            # Some computational predicates are not liquid until evaluated.
            # Their types are checked on the subsequent core pass.
            try:
                ty = type_to_core(representable(node.var_type))
            except LiquefactionException:
                ty = None
            nested = local.with_var(node.var_name, ty) if ty is not None else local
            from aeon.verification.decidability import _location_in_file

            authored = _location_in_file(node.loc, source_path) or (
                source_path == "<stdin>" and getattr(node.loc, "file", None) is None
            )
            if authored:
                check_type(node.var_type, nested)
                visit(node.var_value, nested, node.var_type)
            visit(node.body, nested)
        elif isinstance(node, SType):
            check_type(node, local)
        elif isinstance(node, STerm) and is_dataclass(node):
            for field in fields(node):
                value = getattr(node, field.name)
                if isinstance(value, (STerm, SType)):
                    visit(value, local)

    visit(term, ctx)
