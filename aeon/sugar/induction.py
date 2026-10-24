"""Expand structural induction into checked recursive definitions and matches."""

from dataclasses import fields, replace

from aeon.errors import ProofElaborationError
from aeon.sugar.program import SInduction, STerm, SMatch, SMatchBranch, SVar, SApplication, SQualifiedVar
from aeon.sugar.stypes import SRefinedType, STypeConstructor
from aeon.sugar.proofs import sequence


def expand_induction(program, imported_inductives):
    datatypes = list(program.inductive_decls) + list(imported_inductives)

    def carrier(ty):
        while isinstance(ty, SRefinedType):
            ty = ty.type
        return ty

    definitions = []
    for definition in program.definitions:
        metrics = list(definition.decreasing_by)

        def expand(term):
            if isinstance(term, SInduction):
                target = next((ty for name, ty in definition.args if name.name == term.scrutinee.name), None)
                target = carrier(target)
                if not isinstance(target, STypeConstructor):
                    raise ProofElaborationError("induction requires a named datatype parameter.", loc=term.loc)
                datatype = next((d for d in datatypes if d.name.name == target.name.name), None)
                if datatype is None:
                    raise ProofElaborationError(f"No inductive declaration found for {target.name.name}.", loc=term.loc)
                branches = []
                for branch in term.branches:
                    constructor = next(
                        (c for c in datatype.constructors if c.name.name == branch.constructor.name), None
                    )
                    if constructor is None:
                        raise ProofElaborationError(
                            f"Unknown induction constructor {branch.constructor}.", loc=branch.loc
                        )
                    recursive = [
                        i
                        for i, (_, ty) in enumerate(constructor.args)
                        if isinstance(carrier(ty), STypeConstructor) and carrier(ty).name.name == datatype.name.name
                    ]
                    arity = len(constructor.args)
                    if len(branch.binders) != arity + len(recursive):
                        raise ProofElaborationError(
                            f"Induction case {branch.constructor} expects {arity} fields and {len(recursive)} induction hypotheses.",
                            loc=branch.loc,
                        )
                    facts = []
                    for i, ih in zip(recursive, branch.binders[arity:], strict=True):
                        call = SVar(definition.name, loc=branch.loc)
                        for name, _ in definition.args:
                            arg = branch.binders[i] if name.name == term.scrutinee.name else name
                            call = SApplication(call, SVar(arg, loc=branch.loc), loc=branch.loc)
                        facts.append((ih, call))
                    branches.append(
                        replace(
                            branch,
                            binders=branch.binders[:arity],
                            body=sequence(facts, expand(branch.body), branch.loc),
                        )
                    )
                if not metrics:
                    measure = next((m for m in datatype.measures if m.name.name == "structuralRank"), None)
                    if measure is None:
                        raise ProofElaborationError(
                            "Provide decreasing_by [...] for induction on this datatype.", loc=term.loc
                        )
                    metrics.append(
                        SApplication(
                            SQualifiedVar(datatype.name.name, measure.name, loc=term.loc),
                            SVar(term.scrutinee, loc=term.loc),
                            loc=term.loc,
                        )
                    )
                return SMatch(SVar(term.scrutinee, loc=term.loc), branches, loc=term.loc)
            if isinstance(term, STerm):
                updates = {}
                for field in fields(term):
                    value = getattr(term, field.name)
                    if isinstance(value, STerm):
                        updates[field.name] = expand(value)
                    elif isinstance(value, list) and value and isinstance(value[0], SMatchBranch):
                        updates[field.name] = [replace(b, body=expand(b.body)) for b in value]
                return replace(term, **updates) if updates else term
            return term

        body = expand(definition.body)
        definitions.append(replace(definition, body=body, decreasing_by=metrics))
    return replace(program, definitions=definitions)
