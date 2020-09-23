from typing import List, Callable, Dict
from functools import reduce
from aeon.types import TypeException, Type, TypingContext, BasicType, AbstractionType, TypeAbstraction, \
    IntersectionType, SumType, TypeApplication, RefinedType, top, bottom
from aeon.typechecker.substitutions import substitution_type_in_type
from aeon.typechecker.type_simplifier import reduce_type


class VariableState(object):
    def __init__(self, name: str):
        self.lower_bounds = []
        self.upper_bounds = []
        self.name = str(name)

    def __str__(self):
        return "var({} l={} u={})".format(self.name, self.lower_bounds, self.upper_bounds)


def constrain(ctx: TypingContext, t1: Type, t2: Type, constraints: Dict[str, VariableState]):
    if isinstance(t1, RefinedType):
        constrain(ctx, t1.type, t2, constraints)
        return
    if isinstance(t2, RefinedType):
        constrain(ctx, t1, t2.type, constraints)
        return
    if isinstance(t1, BasicType) and isinstance(t2, BasicType) and t1 == t2:
        return

    if isinstance(t1, BasicType) and t1.name in constraints.keys() and isinstance(t2, BasicType) and t2.name in constraints.keys():
        constraints[t1.name].upper_bounds.append(t2)
        constraints[t2.name].lower_bounds.append(t1)
    elif isinstance(t1, BasicType) and t1.name in constraints.keys():
        constraints[t1.name].upper_bounds.append(t2)
        for t in constraints[t1.name].lower_bounds:
            constrain(ctx, t, t2, constraints)
    elif isinstance(t2, BasicType) and t2.name in constraints.keys():
        constraints[t2.name].lower_bounds.append(t1)
        for t in constraints[t2.name].upper_bounds:
            constrain(ctx, t1, t, constraints)

    if isinstance(t1, AbstractionType) and isinstance(t2, AbstractionType):
        constrain(ctx, t2.arg_type, t1.arg_type, constraints)
        constrain(ctx, t1.return_type, t2.return_type, constraints)

    if isinstance(t1, TypeApplication) and isinstance(t2, TypeApplication):
        constrain(ctx, t1.target, t2.target, constraints)
        constrain(ctx, t1.argument, t2.argument, constraints)  # TODO: variance?


def collapse(t: BasicType, explored: List[VariableState], polarity : bool, constraints : Dict[str, VariableState]):
    if polarity:
        r : Type = top
        if t.name not in explored:
            for high in constraints[t.name].upper_bounds:
                if isinstance(high, BasicType) and high.name in constraints.keys():
                    high = collapse(high, explored + [t.name], not polarity, constraints)
                r = IntersectionType(r, high)
    else:
        r : Type = bottom
        if t.name not in explored:
            for low in constraints[t.name].lower_bounds:
                if isinstance(low, BasicType) and low.name in constraints.keys():
                    low = collapse(low, explored + [t.name], not polarity, constraints)
                r = SumType(r, low)
    r = reduce_type(None, r)
    return r


counter = 0
def fresh_type_inference_var():
    global counter
    counter += 1
    return "fresh_{}".format(counter)

def unification(ctx: TypingContext,
                t1: Type,
                t2: Type) -> Type:
    type_variables = []
    original_t1 = t1

    variables_to_track : Dict[str, VariableState] = {}
    while isinstance(t1, TypeAbstraction):
        v = VariableState(t1.name)
        variables_to_track[v.name] = v
        type_variables.append(v)
        t1 = t1.type
    while isinstance(t2, TypeAbstraction):
        v = VariableState(t2.name)
        variables_to_track[v.name] = v
        t2 = t2.type

    constrain(ctx, t1, t2, variables_to_track)
    l = [ collapse(t, [], True, variables_to_track) for t in type_variables ]
    r = reduce( lambda x, y: TypeApplication(x, y), l, original_t1 )
    return r
