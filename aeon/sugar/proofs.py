"""Surface proof notation elaborates to ordinary checked Aeon expressions."""

from aeon.errors import ProofElaborationError
from aeon.sugar.program import SAnnotation, SApplication, SLet, SLiteral, SVar
from aeon.sugar.stypes import SRefinedType, STypeConstructor
from aeon.utils.name import Name, fresh_counter


def unit(loc):
    return SLiteral(None, STypeConstructor(Name("Unit", 0)), loc=loc)


def proposition(predicate, loc):
    return SRefinedType(Name("_proof", fresh_counter.fresh()), STypeConstructor(Name("Unit", 0)), predicate, loc=loc)


def equality(left, right, loc):
    return SApplication(SApplication(SVar(Name("==", 0), loc=loc), left, loc=loc), right, loc=loc)


def sequence(bindings, result, loc):
    for name, proof in reversed(bindings):
        result = SLet(name, proof, result, loc=loc)
    return result


def calc(steps, loc):
    bindings = []
    previous = None
    first = None
    for left, right, proof in steps:
        if left is None:
            if previous is None:
                raise ProofElaborationError("The first calc step must specify its left-hand side.", loc)
            left = previous
        if first is None:
            first = left
        elif left != previous:
            # Check continuity too; spelling a different expression must not
            # silently turn two unrelated equalities into a chain.
            bindings.append(
                (
                    Name("_calc_join", fresh_counter.fresh()),
                    SAnnotation(unit(loc), proposition(equality(previous, left, loc), loc), loc=loc),
                )
            )
        # Elaborate endpoints as values as well as logical terms. This retains
        # checked result contracts of nested calls, just like ordinary lets.
        bindings.append((Name("_calc_left", fresh_counter.fresh()), left))
        bindings.append((Name("_calc_right", fresh_counter.fresh()), right))
        bindings.append(
            (
                Name("_calc_step", fresh_counter.fresh()),
                SAnnotation(proof, proposition(equality(left, right, loc), loc), loc=loc),
            )
        )
        previous = right
    return SAnnotation(sequence(bindings, unit(loc), loc), proposition(equality(first, previous, loc), loc), loc=loc)
