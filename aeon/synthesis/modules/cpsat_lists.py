"""Expand fixed-length list holes into constructor spines with scalar leaves.

Length is inferred from checked constructor equations (zero / tail + one),
not from a measure's spelling. The result remains an ordinary Aeon term and
is validated against the original program before the backend returns it.
"""

from dataclasses import dataclass, field

from aeon.core.equality import core_type_equality
from aeon.core.instantiation import type_substitution
from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidTerm, LiquidVar
from aeon.core.substitutions import instantiate_refinement_in_type, substitution_in_liquid, substitution_in_type
from aeon.core.terms import Annotation, Application, Hole, Let, Rec, RefinementApplication, Term, TypeApplication, Var
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    RefinementPolymorphism,
    Type,
    TypeConstructor,
    TypePolymorphism,
)
from aeon.synthesis.api import UnsupportedSynthesisGoal
from aeon.synthesis.grammar.poly import predicate_argument
from aeon.typechecking.branch_evidence import stored_match_predicate
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name, fresh_counter


def _fresh(label: str) -> Name:
    return Name(label, fresh_counter.fresh())


def _base(ty: Type) -> Type:
    return ty.type if isinstance(ty, RefinedType) else ty


def _equations(predicate: LiquidTerm):
    """Only positive conjuncts imply a fixed length or a constructor equation."""
    if isinstance(predicate, LiquidApp):
        if predicate.fun.name == "&&":
            for child in predicate.args:
                yield from _equations(child)
        elif predicate.fun.name == "==" and len(predicate.args) == 2:
            yield tuple(predicate.args)
            yield tuple(reversed(predicate.args))


def _measure_equations(ty: Type):
    if isinstance(ty, RefinedType):
        for lhs, rhs in _equations(ty.refinement):
            if isinstance(lhs, LiquidApp) and lhs.args == [LiquidVar(ty.name)]:
                yield lhs.fun, rhs


@dataclass
class _Constructor:
    head: Term
    fields: list[AbstractionType]
    result: Type


def _instantiate(name: Name, ty: Type, actual: TypeConstructor, ctx: TypingContext) -> _Constructor:
    head: Term = Var(name)
    type_index = relation_index = 0
    while isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
        if isinstance(ty, TypePolymorphism):
            if type_index >= len(actual.args):
                raise UnsupportedSynthesisGoal("CPSatHole cannot instantiate this list constructor's type parameters.")
            arg = actual.args[type_index]
            head = TypeApplication(head, arg)
            ty = type_substitution(ty.body, ty.name, arg)
            type_index += 1
        else:
            predicate = stored_match_predicate(actual, relation_index, ty.sort)
            argument = predicate_argument(ctx, predicate, ty.sort)
            head = RefinementApplication(head, argument)
            ty = instantiate_refinement_in_type(ty.body, ty.name, predicate)
            relation_index += 1
    fields = []
    while isinstance(ty, AbstractionType):
        fields.append(ty)
        ty = ty.type
    return _Constructor(head, fields, ty)


@dataclass
class ListExpansion:
    term: Term
    template: Term
    leaves: dict[Name, Type] = field(default_factory=dict)
    guards: set[Name] = field(default_factory=set)
    bindings: dict[Name, Type] = field(default_factory=dict)
    constraints: list[LiquidTerm] = field(default_factory=list)
    result_name: Name | None = None

    def guard(self, value: Term, ty: Type) -> Term:
        if not isinstance(ty, RefinedType):
            return value
        binder = _fresh("list_refinement")
        self.guards.add(binder)
        predicate = substitution_in_liquid(ty.refinement, LiquidVar(binder), ty.name)
        return Annotation(value, RefinedType(binder, ty.type, predicate))


def expand_list(hole: Name, ty: Type, constructors: list[Rec], ctx: TypingContext) -> ListExpansion:
    return expand_list_schema(hole, ty, [(c.var_name, c.var_type) for c in constructors], ctx)


def expand_list_schema(
    hole: Name, ty: Type, constructors: list[tuple[Name, Type]], ctx: TypingContext
) -> ListExpansion:
    """Support nil/cons ADTs with one recursive tail and one scalar field."""
    actual = _base(ty)
    error = (
        f"CPSatHole cannot handle hole {hole.pretty()}: expected a fixed-length list with Bool, Int or Float elements"
    )
    if not isinstance(ty, RefinedType) or not isinstance(actual, TypeConstructor):
        raise UnsupportedSynthesisGoal(error)

    matching = []
    for name, constructor_type in constructors:
        result_type = constructor_type
        while isinstance(result_type, (TypePolymorphism, RefinementPolymorphism, AbstractionType)):
            result_type = result_type.type if isinstance(result_type, AbstractionType) else result_type.body
        base = _base(result_type)
        if isinstance(base, TypeConstructor) and base.name == actual.name:
            matching.append(_instantiate(name, constructor_type, actual, ctx))
    nil = next((c for c in matching if not c.fields), None)
    cons = next((c for c in matching if len(c.fields) == 2), None)
    if len(matching) != 2 or nil is None or cons is None:
        raise UnsupportedSynthesisGoal(error)
    tails = [i for i, f in enumerate(cons.fields) if core_type_equality(_base(f.var_type), actual)]
    if len(tails) != 1:
        raise UnsupportedSynthesisGoal(error)
    tail_index = tails[0]
    element = _base(cons.fields[1 - tail_index].var_type)
    if not isinstance(element, TypeConstructor) or element.name not in {
        Name("Bool", 0),
        Name("Int", 0),
        Name("Float", 0),
    }:
        raise UnsupportedSynthesisGoal(error)

    length_measures = set()
    zero_measures = {name for name, rhs in _measure_equations(nil.result) if rhs == LiquidLiteralInt(0)}
    for measure, rhs in _measure_equations(cons.result):
        if measure not in zero_measures or not isinstance(rhs, LiquidApp) or rhs.fun != Name("+", 0):
            continue
        tail_measure = LiquidApp(measure, [LiquidVar(cons.fields[tail_index].var_name)])
        if rhs.args in ([tail_measure, LiquidLiteralInt(1)], [LiquidLiteralInt(1), tail_measure]):
            length_measures.add(measure)
    lengths = [
        rhs.value
        for measure, rhs in _measure_equations(ty)
        if measure in length_measures and isinstance(rhs, LiquidLiteralInt)
    ]
    if not lengths:
        raise UnsupportedSynthesisGoal(error + "; require a literal equality on a zero / tail + 1 measure")
    length = lengths[0]
    if length < 0 or length > 1000:
        raise UnsupportedSynthesisGoal("CPSatHole fixed list length must be between 0 and 1000.")

    expansion = ListExpansion(nil.head, nil.head)
    constructor = _fresh("list_cons")
    previous = _fresh("list_nil")
    bindings: list[tuple[Name, Term, Term]] = [(constructor, cons.head, cons.head), (previous, nil.head, nil.head)]
    expansion.bindings[previous] = nil.result
    for index in range(length):
        application: Term = Var(constructor)
        template_application: Term = Var(constructor)
        field_type: Type = cons.fields[0]
        for position in range(2):
            assert isinstance(field_type, AbstractionType)
            if position == tail_index:
                argument: Term = Var(previous)
                checked_argument = expansion.guard(argument, field_type.var_type)
            else:
                leaf = _fresh(f"{hole.name}_{length - index - 1}")
                expansion.leaves[leaf] = field_type.var_type
                expansion.bindings[leaf] = field_type.var_type
                argument = Hole(leaf)
                checked_argument = argument
                if position == 0:
                    # Later field refinements can refer to an earlier element.
                    element_name = _fresh("list_element")
                    bindings.append((element_name, argument, argument))
                    # Relate the runtime alias to the scalar witness as well.
                    expansion.bindings[element_name] = RefinedType(
                        element_name, element, LiquidApp(Name("==", 0), [LiquidVar(element_name), LiquidVar(leaf)])
                    )
                    argument = checked_argument = Var(element_name)
            application = Application(application, checked_argument)
            template_application = Application(template_application, argument)
            witness = Var(argument.name) if isinstance(argument, Hole) else argument
            assert isinstance(witness, Var)
            if isinstance(field_type.var_type, RefinedType):
                required = field_type.var_type
                expansion.constraints.append(
                    substitution_in_liquid(required.refinement, LiquidVar(witness.name), required.name)
                )
            field_type = substitution_in_type(field_type.type, witness, field_type.var_name)
        previous = _fresh("list_node")
        expansion.bindings[previous] = field_type
        bindings.append((previous, application, template_application))
    result = expansion.guard(Var(previous), ty)
    template: Term = Var(previous)
    for name, value, template_value in reversed(bindings):
        result = Let(name, value, result)
        template = Let(name, template_value, template)
    expansion.term = result
    # Solver guards must not weaken literal/tail selfification when checking
    # the finished term. Its original type and constructor types check them.
    expansion.template = template
    expansion.result_name = previous
    return expansion
