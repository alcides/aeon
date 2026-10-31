"""MATCH through Aeon's existing lowered datatype eliminators."""

from aeon.core.instantiation import type_substitution
from aeon.core.substitutions import (
    substitution_in_type,
    instantiate_refinement_in_type,
    instantiate_refinement_with_horn_in_type,
)
from aeon.core.terms import Abstraction, Application, TypeApplication, RefinementApplication, Literal, Hole, Var, Let
from aeon.core.types import (
    AbstractionType,
    TypePolymorphism,
    RefinementPolymorphism,
    TypeConstructor,
    RefinedType,
    ExistentialType,
    t_bool,
    t_int,
    t_float,
    t_string,
)
from aeon.synthesis.modules.synquid.constraints import fresh_name
from aeon.synthesis.modules.synquid.round_trip import erase
from aeon.synthesis.modules.synquid.solver import Status
from aeon.typechecking.branch_evidence import (
    match_branch_evidence,
    match_refinement_obligation,
    unconstrained_predicate,
)
from aeon.typechecking.typeinfer import check, synth
from aeon.typechecking.well_formed import wellformed
from aeon.errors import AeonError
from aeon.verification.constructor_registry import get_constructor_groups


def _predicate_term(predicate, assignment):
    """Close a solved logical predicate as the recursor's explicit argument."""
    from aeon.core.liquid import (
        LiquidApp,
        LiquidVar,
        LiquidLiteralBool,
        LiquidLiteralInt,
        LiquidLiteralFloat,
        LiquidLiteralString,
    )
    from aeon.core.terms import If
    from aeon.verification.horn import apply_liquid

    def term(liquid):
        if isinstance(liquid, LiquidVar):
            return Var(liquid.name)
        for cls, ty in (
            (LiquidLiteralBool, t_bool),
            (LiquidLiteralInt, t_int),
            (LiquidLiteralFloat, t_float),
            (LiquidLiteralString, t_string),
        ):
            if isinstance(liquid, cls):
                return Literal(liquid.value, ty)
        if isinstance(liquid, LiquidApp):
            args = [term(a) for a in liquid.args]
            if liquid.fun.name == "ite" and len(args) == 3:
                return If(*args)
            result = Var(liquid.fun)
            for arg in args:
                result = Application(result, arg)
            return result
        raise NotImplementedError("Unresolved match predicate")

    result = term(apply_liquid(assignment, predicate))
    for arg, _ in reversed(predicate.argtypes):
        assert isinstance(arg, LiquidVar)
        result = Abstraction(arg.name, result)
    return result


def match_terms(ctx, level, goal, skip, mem, state, *, only=None, fixed_case=None):
    from aeon.synthesis.modules.synquid.engine import synthes_memory, _local_check, _materialize_term

    if state.match_depth >= mem.get("synquid_match_depth", level):
        return
    groups = get_constructor_groups()
    datatypes = set()
    for _, ty in ctx.concrete_vars():
        while isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
            ty = ty.body
        while isinstance(ty, AbstractionType):
            ty = ty.type
        ty = erase(ty)
        if isinstance(ty, TypeConstructor) and ty.name.name in groups and wellformed(ctx, ty):
            datatypes.add(ty)
    seen = set()

    def datatype_shapes():
        yield from sorted(datatypes, key=repr)
        if level <= 0 or only is not None:
            return
        # An application can discover an instantiation absent from every
        # in-scope value (e.g. Box (Box Int)). Infer such scrutinee shapes from
        # component signatures and arguments instead of guessing a catalogue.
        from aeon.synthesis.modules.synquid.inference import infer_terms

        for candidate in infer_terms(ctx, level, skip, mem, state):
            ty = erase(candidate.state.resolve(candidate.type))
            if not isinstance(ty, TypeConstructor) or ty.name.name not in groups:
                continue
            if candidate.state.finalize() in (Status.INVALID, Status.EXHAUSTED):
                continue
            ty = erase(candidate.state.resolve(candidate.type))
            if ty not in datatypes and wellformed(ctx, ty):
                datatypes.add(ty)
                yield ty

    for datatype in datatype_shapes():
        rec = next(((n, t) for n, t in ctx.concrete_vars() if n.name == datatype.name.name + "_rec"), None)
        if rec is None:
            continue
        rec_name, rec_type = rec
        scrutinees = (
            [Var(only)]
            if only is not None and erase(ctx.type_of(only)) == datatype
            else []
            if only is not None
            else synthes_memory(ctx, level, datatype, skip, mem, state, conditionals=False)
        )
        for scrutinee in scrutinees:
            if repr(scrutinee) in seen or isinstance(scrutinee, Var) and scrutinee.name in state.matched:
                continue
            seen.add(repr(scrutinee))
            child = state.fork()
            body_ctx = ctx
            scrut = scrutinee
            try:
                vc, actual = synth(child.resolve_context(child.context), scrutinee)
                child.add(vc)
                actual = child.resolve(actual)
                if isinstance(actual, ExistentialType):
                    for binder, ty in actual.binders:
                        child.bind(binder, ty)
                        body_ctx = body_ctx.with_var(binder, ty)
                    actual = actual.body
            except (AssertionError, NotImplementedError, AeonError):
                continue
            precise = actual.type if isinstance(actual, RefinedType) else actual
            if not isinstance(precise, TypeConstructor) or erase(precise) != datatype:
                continue
            if not isinstance(scrut, Var):
                witness = fresh_name("scrutinee")
                child.bind(witness, actual)
                body_ctx = body_ctx.with_var(witness, actual)
                scrut = Var(witness)
            child.match_depth += 1
            child.matched |= {scrut.name}
            inst = rec_type
            safe_inst = rec_type
            spine = []
            # Fig. 4 MATCH: constructor fields use the scrutinee's precise
            # arguments. Erasure is only for enumerating compatible shapes.
            args = iter(precise.args)
            while isinstance(inst, (TypePolymorphism, RefinementPolymorphism)):
                if isinstance(inst, TypePolymorphism):
                    arg = next(args, None)
                    # The final type parameter is the result motive.
                    arg = erase(goal) if arg is None else arg
                    spine.append(("T", arg))
                    assert isinstance(safe_inst, TypePolymorphism)
                    safe_inst = type_substitution(safe_inst.body, safe_inst.name, arg)
                    inst = type_substitution(inst.body, inst.name, arg)
                else:
                    predicate = child.refinement_parameter(inst.sort)
                    spine.append(("R", predicate))
                    assert isinstance(safe_inst, RefinementPolymorphism)
                    safe_inst = instantiate_refinement_in_type(
                        safe_inst.body, safe_inst.name, unconstrained_predicate(safe_inst.sort)
                    )
                    inst = instantiate_refinement_with_horn_in_type(inst.body, inst.name, inst.sort, predicate.name)
            if not isinstance(inst, AbstractionType):
                continue
            child.subtype(actual, inst.var_type)
            rest = substitution_in_type(inst.type, scrut, inst.var_name)
            assert isinstance(safe_inst, AbstractionType)
            safe_rest = substitution_in_type(safe_inst.type, scrut, safe_inst.var_name)
            cases = []
            while isinstance(rest, AbstractionType):
                assert isinstance(safe_rest, AbstractionType)
                case_name, case_type = rest.var_name, rest.var_type
                fields = []
                expected = case_type
                while isinstance(expected, AbstractionType):
                    n = fresh_name(expected.var_name.name)
                    fields.append(n)
                    expected = substitution_in_type(expected.type, Var(n), expected.var_name)
                skeleton = Hole(fresh_name("case"))
                for n in reversed(fields):
                    skeleton = Abstraction(n, skeleton)
                if any(kind == "R" for kind, _ in spine):
                    child.add(
                        match_refinement_obligation(
                            child.context, skeleton, safe_rest.var_type, case_type, datatype.name.name, case_name, scrut
                        )
                    )
                evidence = match_branch_evidence(
                    child.context, skeleton, case_type, datatype.name.name, case_name, scrut
                )
                cases.append((case_name, fields, evidence))
                rest = rest.type
                safe_rest = safe_rest.type
            if child.solve() in (Status.INVALID, Status.EXHAUSTED):
                continue

            def handlers(index, bodies, partial):
                if index == len(cases):
                    if partial.finalize() in (Status.INVALID, Status.EXHAUSTED):
                        return
                    for assignment in partial.assignments:
                        term = Var(rec_name)
                        for kind, arg in spine:
                            term = (
                                TypeApplication(term, partial.materialize(arg, assignment))
                                if kind == "T"
                                else RefinementApplication(term, _predicate_term(arg, assignment))
                            )
                        term = Application(term, scrut)
                        for body in bodies:
                            term = Application(term, _materialize_term(body, assignment, partial))
                        if _local_check(body_ctx, term, goal, partial):
                            state.stats.matches += 1
                            yield term if scrut is scrutinee else Let(scrut.name, scrutinee, term)
                    return
                case_name, fields, evidence = cases[index]
                if evidence is None:
                    return
                branch = partial.fork()
                branch_ctx = body_ctx
                for n, ty in evidence.fields:
                    branch.bind(n, ty)
                    branch_ctx = branch_ctx.with_var(n, ty)
                branch = branch.assume(evidence.fact)
                if branch.inhabited() == Status.VALID:
                    return
                candidates = (
                    [fixed_case[1]]
                    if fixed_case is not None and case_name.name == fixed_case[0]
                    else synthes_memory(branch_ctx, level, goal, skip, mem, branch)
                )
                for body in candidates:
                    selected = branch.fork()
                    try:
                        selected.add(check(selected.context, body, goal))
                    except (AssertionError, NotImplementedError, AeonError):
                        continue
                    if selected.solve() in (Status.INVALID, Status.EXHAUSTED):
                        continue
                    handler = body
                    for n in reversed(fields):
                        handler = Abstraction(n, handler)
                    # Constraints are already closed over this branch's
                    # fields/path. Share their predicate solution with sibling
                    # cases without leaking any branch-local assumptions.
                    yield from handlers(index + 1, bodies + [handler], selected.fork(partial.context))

            yield from handlers(0, [], child)


def abduced_matches(ctx, level, goal, skip, mem, state):
    """§3.4: abduce a scalar-constructor case before guessing a scrutinee.

    The original MATCH enumeration remains the fallback, including datatypes
    without scalar constructors and scrutinees computed by applications.
    """
    from itertools import islice
    from aeon.core.liquid import LiquidApp, LiquidVar
    from aeon.core.types import extract_parts
    from aeon.core.substitutions import substitution_in_liquid
    from aeon.synthesis.modules.synquid.abduction import abduce
    from aeon.synthesis.modules.synquid.engine import synthes_memory
    from aeon.utils.name import Name
    from aeon.verification.vcs import LiquidConstraint

    if state.match_depth >= mem.get("synquid_match_depth", level):
        return
    facts = []
    groups = get_constructor_groups()
    for variable, datatype in ctx.concrete_vars():
        datatype = erase(datatype)
        if skip(variable) or variable in state.matched or not isinstance(datatype, TypeConstructor):
            continue
        for constructor, schema in ctx.concrete_vars():
            if constructor.name not in groups.get(datatype.name.name, set()):
                continue
            while isinstance(schema, (TypePolymorphism, RefinementPolymorphism)):
                schema = schema.body
            if isinstance(schema, AbstractionType):
                continue
            binder, _, predicate = extract_parts(schema)
            fact = LiquidApp(
                Name("&&", 0),
                [
                    substitution_in_liquid(predicate, LiquidVar(variable), binder),
                    LiquidApp(Name("==", 0), [LiquidVar(variable), LiquidVar(constructor)]),
                ],
            )
            facts.append((fact, variable, "case_" + constructor.name[len(datatype.name.name) + 1 :]))
    if not facts:
        return
    qualifiers = frozenset(fact for fact, _, _ in facts)
    proposed = state.fork()
    path = proposed.fresh_predicate(ctx, qualifiers)
    proposed = proposed.assume(path)
    for branch in islice(synthes_memory(ctx, level, goal, skip, mem, proposed, conditionals=False), 64):
        result = abduce(state, branch, goal, qualifiers=qualifiers)
        for condition in result.conditions:
            for fact, variable, case in facts:
                region = state.assume(fact)
                if region.inhabited() != Status.INVALID:
                    continue
                if region.query.valid(region.lift(LiquidConstraint(condition))) == Status.VALID:
                    state.stats.match_abductions += 1
                    yield from match_terms(ctx, level, goal, skip, mem, state, only=variable, fixed_case=(case, branch))
