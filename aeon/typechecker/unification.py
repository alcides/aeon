from aeon.typechecker.substitutions import substitution_type_in_type
from typing import List, Callable, Dict
from functools import reduce
from aeon.types import ExistentialType, TypeException, Type, TypingContext, BasicType, AbstractionType, TypeAbstraction, \
    IntersectionType, UnionType, TypeApplication, RefinedType, top, bottom, find_basic_types, shape, star

from aeon.typechecker.ast_helpers import smt_not

class UnificationError(Exception):
    pass

class VariableState(object):
    def __init__(self, name: str):
        self.lower_bounds = []
        self.upper_bounds = []
        self.name = str(name)
        self.kind = star # TODO: check kinds in Variable States

    def __str__(self):
        return "var({} l={} u={})".format(self.name, self.lower_bounds, self.upper_bounds)

def is_var(t:Type, constraints: Dict[str, VariableState]):
    return isinstance(t, BasicType) and t.name in constraints.keys()

def constrain(ctx: TypingContext, t1: Type, t2: Type, constraints: Dict[str, VariableState]):

    if isinstance(t1, BasicType) and isinstance(t2, BasicType) and t1 == t2:
        pass
    elif is_var(t1, constraints) and is_var(t2, constraints):
        constraints[t1.name].upper_bounds.append(t2)
        constraints[t2.name].lower_bounds.append(t1)

    elif is_var(t1, constraints) and isinstance(t2, AbstractionType):
        k1 = BasicType(ctx.fresh_var())
        k2 = BasicType(ctx.fresh_var())
        constraints[k1.name] = VariableState(k1.name)
        constraints[k2.name] = VariableState(k2.name)
        replacement = AbstractionType(t2.arg_name, k1, k2)
        constraints[t1.name].lower_bounds.append(replacement)
        constraints[t1.name].upper_bounds.append(replacement)
        constrain(ctx, t2.arg_type, k1, constraints)
        constrain(ctx.with_var(t2.arg_name, t2.arg_type), k2, t2.return_type, constraints)

    elif isinstance(t1, AbstractionType) and is_var(t2, constraints):
        k1 = BasicType(ctx.fresh_var())
        k2 = BasicType(ctx.fresh_var())
        constraints[k1.name] = VariableState(k1.name)
        constraints[k2.name] = VariableState(k2.name)
        replacement = AbstractionType(t1.arg_name, k1, k2)
        constraints[t2.name].lower_bounds.append(replacement)
        constraints[t2.name].upper_bounds.append(replacement)
        constrain(ctx, k1, t1.arg_type, constraints)
        constrain(ctx.with_var(t1.arg_name, k1), t1.return_type, k2, constraints)

    elif is_var(t1, constraints):
        constraints[t1.name].upper_bounds.append(t2)
        for t in constraints[t1.name].lower_bounds:
            constrain(ctx, t, t2, constraints)

    elif is_var(t2, constraints):
        constraints[t2.name].lower_bounds.append(t1)
        for t in constraints[t2.name].upper_bounds:
            constrain(ctx, t1, t, constraints)

    elif isinstance(t1, AbstractionType) and isinstance(t2, AbstractionType):
        constrain(ctx, t2.arg_type, t1.arg_type, constraints)
        constrain(ctx, t1.return_type, t2.return_type, constraints)

    elif isinstance(t1, TypeApplication) and isinstance(t2, TypeApplication):
        constrain(ctx, t1.target, t2.target, constraints)
        constrain(ctx, t1.argument, t2.argument, constraints)  # TODO: variance?

    elif isinstance(t1, ExistentialType):
        constrain(ctx, t1.right, t2, constraints) #.with_var(t1.left_name, t1.left)

    elif isinstance(t2, ExistentialType):
        constrain(ctx, t1, t2.right, constraints) # .with_var(t2.left_name, t2.left) # TODO: is this correct?

    elif isinstance(t1, IntersectionType):
        if isinstance(t1.right, RefinedType):
            talt = RefinedType(t1.right.name, shape(t2), smt_not(t1.right.cond))
            constrain(ctx, t1.left, UnionType(t2, talt), constraints)
        else:
            constrain(ctx, t1.left, t2, constraints)

        if isinstance(t1.left, RefinedType):
            talt = RefinedType(t1.left.name, shape(t2), smt_not(t1.left.cond))
            constrain(ctx, t1.right, UnionType(t2, talt), constraints)
        else:
            constrain(ctx, t1.right, t2, constraints)

    elif isinstance(t2, UnionType):
        constrain(ctx, t1, t2.left, constraints)
        constrain(ctx, t1, t2.right, constraints)

    elif isinstance(t1, IntersectionType):
        constrain(ctx, t1.left, t2, constraints)
        constrain(ctx, t1.right, t2, constraints)

    elif isinstance(t2, UnionType):
        constrain(ctx, t1, t2.left, constraints)
        constrain(ctx, t1, t2.right, constraints)

    elif isinstance(t1, RefinedType):
        talt = RefinedType(t1.name, shape(t2), smt_not(t1.cond))
        constrain(ctx, t1.type, UnionType(t2, talt), constraints)
    elif isinstance(t2, RefinedType):
        constrain(ctx, t1, t2.type, constraints)
    else:
        raise UnificationError("Unification Failed: {} <: {}".format(t1, t2) )


def collapse(t: BasicType, explored: List[VariableState], polarity : bool, constraints : Dict[str, VariableState]):

    if polarity:
        r : Type = top
        if t.name not in explored:
            for high in constraints[t.name].upper_bounds:
                if isinstance(high, BasicType) and high.name in constraints.keys():
                    high = collapse(high, explored + [t.name], not polarity, constraints)
                r = IntersectionType(r, high)
        else:
            r = BasicType(t)
    else:
        r : Type = bottom
        if t.name not in explored:
            for low in constraints[t.name].lower_bounds:
                if isinstance(low, BasicType) and low.name in constraints.keys():
                    low = collapse(low, explored + [t.name], not polarity, constraints)
                r = UnionType(r, low)
        else:
            r = BasicType(t)
    return r




def unification(ctx: TypingContext,
                t1: Type,
                t2: Type) -> Type:
    type_variables = []
    type_kinds = {}
    original_t1 = t1

    variables_to_track : Dict[str, VariableState] = {}
    while isinstance(t1, TypeAbstraction):
        v = VariableState(t1.name)
        variables_to_track[v.name] = v
        type_variables.append(v)
        type_kinds[t1.name] = t1.kind
        t1 = t1.type
    while isinstance(t2, TypeAbstraction):
        v = VariableState(t2.name)
        variables_to_track[v.name] = v
        t2 = t2.type

    constrain(ctx, t1, t2, variables_to_track)
    l = [ collapse(t, [], True, variables_to_track) for t in type_variables ]
    r = reduce( lambda x, y: TypeApplication(x, y), l, original_t1 )
    bts = find_basic_types(r)
    variables_to_abstract = [(t, type_kinds[t]) for t in variables_to_track.keys() if t in bts]
    r = reduce( lambda y, a: TypeAbstraction(a[0], a[1], y), variables_to_abstract, r)
    return r

def unificationEq(ctx: TypingContext,
                t1: Type,
                t2: Type) -> Type:
    type_variables1 = []
    type_kinds1 = {}
    type_variables2 = []
    original_t1 = t1

    variables_to_track : Dict[str, VariableState] = {}
    while isinstance(t1, TypeAbstraction):
        v = VariableState(t1.name)
        variables_to_track[v.name] = v
        type_variables1.append(v)
        type_kinds1[t1.name] = t1.kind
        t1 = t1.type

    while isinstance(t2, TypeAbstraction):
        t2_new_name = str(t2.name) + "__" + ctx.fresh_type_var()
        v = VariableState(t2_new_name)
        variables_to_track[v.name] = v
        type_variables2.append(v)
        type_kinds1[v.name] = t2.kind
        t2 = substitution_type_in_type(t2.type, BasicType(v.name), t2.name)

    constrain(ctx, t1, t2, variables_to_track)
    constrain(ctx, t2, t1, variables_to_track)
    l1 = [ collapse(t, [], True, variables_to_track) for t in type_variables1 ]
    l2 = [ collapse(t, [], True, variables_to_track) for t in type_variables2 ]
    r = reduce( lambda x, y: TypeApplication(x, y), l1, original_t1 )
    bts = find_basic_types(r)
    variables_to_abstract = [(t, variables_to_track[t].kind) for t in variables_to_track.keys() if t in bts]
    r = reduce( lambda y, a: TypeAbstraction(a[0], a[1], y), variables_to_abstract, r)
    return r
