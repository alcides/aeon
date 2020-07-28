from typing import List, Callable
from functools import reduce
from aeon.types import TypeException, Type, TypingContext, BasicType, AbstractionType, TypeAbstraction, \
    IntersectionType, SumType, TypeApplication, RefinedType, top, bottom
from aeon.typechecker.substitutions import substitution_type_in_type
from aeon.typechecker.type_simplifier import reduce_type


class VariableState(object):
    def __init__(self, level: int):
        self.level = level
        self.lower_bounds = []
        self.upper_bounds = []


class Variable(Type):
    def __init__(self, original_name: str, state):
        self.state = state
        self.original_name = original_name

    def __deepcopy__(self, memo):
        """ Do not deep copy attributes """
        cls = self.__class__
        result = cls.__new__(cls)
        memo[id(self)] = result
        for k, v in self.__dict__.items():
            setattr(result, k, v)
        return result

    def __str__(self):
        return "var({})".format(self.original_name)


def freshVar(name: str, level: int) -> Variable:
    return Variable(name, VariableState(level))


def get_level_of(t: Type) -> int:
    if isinstance(t, BasicType):
        return 0
    elif isinstance(t, RefinedType):
        return get_level_of(t.type)
    elif isinstance(t, AbstractionType):
        return max(get_level_of(t.arg_type), get_level_of(t.return_type))
    elif isinstance(t, SumType):
        return max(get_level_of(t.left), get_level_of(t.right))
    elif isinstance(t, IntersectionType):
        return max(get_level_of(t.left), get_level_of(t.right))
    elif isinstance(t, TypeApplication):
        return get_level_of(t.target)  # TODO
    elif isinstance(t, TypeAbstraction):
        return get_level_of(t.type)  # TODO
    elif isinstance(t, Variable):
        return t.state.level
    else:
        raise TypeException("No get_level function defined for {}".format(t))


def extrude(t: Type, level: int) -> Type:
    if isinstance(t, BasicType):
        return t
    elif isinstance(t, RefinedType):
        return RefinedType(t.name, extrude(t.type, level), t.cond)
    elif isinstance(t, AbstractionType):
        return AbstractionType(t.arg_name, extrude(t.arg_type, level),
                               extrude(t.return_type, level))
    elif isinstance(t, SumType):
        return SumType(extrude(t.left, level), extrude(t.right, level))
    elif isinstance(t, IntersectionType):
        return IntersectionType(extrude(t.left, level),
                                extrude(t.right, level))
    elif isinstance(t, TypeApplication):
        return TypeApplication(extrude(t.target, level),
                               extrude(t.argument, level))
    elif isinstance(t, TypeAbstraction):
        return TypeAbstraction(t.name, t.kind, extrude(t.type, level))
    elif isinstance(t, Variable):
        return freshVar(t.original_name, level)
    else:
        return t


def constrain(ctx: TypingContext, t1: Type, t2: Type):
    if isinstance(t1, BasicType) and isinstance(t2, BasicType) and t1 == t2:
        pass
    elif isinstance(t1, AbstractionType) and isinstance(t2, AbstractionType):
        constrain(ctx, t2.arg_type, t1.arg_type)
        constrain(ctx, t1.return_type, t2.return_type)
    elif isinstance(t1, Variable):
        if get_level_of(t2) <= get_level_of(t1):
            t1.state.upper_bounds.append(t2)
            for t in t1.state.lower_bounds:
                constrain(ctx, t, t2)
        else:
            r2 = extrude(t2, get_level_of(t1))
            constrain(ctx, r2, t2)
            constrain(ctx, t1, r2)
    elif isinstance(t2, Variable):
        if get_level_of(t1) <= get_level_of(t2):
            t2.state.lower_bounds.append(t1)
            for t in t2.state.upper_bounds:
                constrain(ctx, t1, t)
        else:
            r1 = extrude(t1, get_level_of(t2))
            constrain(ctx, t1, r1)
            constrain(ctx, r1, t2)
    elif isinstance(t1, TypeApplication) and isinstance(t2, TypeApplication):
        constrain(ctx, t1.target, t2.target)
        constrain(ctx, t1.argument, t2.argument)  # TODO: variance?
    else:
        raise TypeException("Cannot constrain types {} and {}".format(t1, t2))


def expand_type_helper(t: Type, polarity: bool,
                       states: List[VariableState]) -> Type:
    if isinstance(t, BasicType):
        return t
    elif isinstance(t, AbstractionType):
        return AbstractionType(
            t.arg_name, expand_type_helper(t.arg_type, not polarity, states),
            expand_type_helper(t.return_type, polarity, states))
    elif isinstance(t, Variable):
        b = BasicType(t.original_name)
        if t.state in states:
            return b
        else:
            bounds = t.state.lower_bounds if polarity else t.state.upper_bounds
            boundTypes: List[Type] = [
                expand_type_helper(ti, polarity, states + [t.state])
                for ti in bounds
            ]
            how_to_merge: Callable[
                [Type, Type], Type] = SumType if polarity else IntersectionType
            default: Type = top if polarity else bottom
            return reduce(how_to_merge, boundTypes, default)
    elif isinstance(t, TypeApplication):
        return TypeApplication(
            expand_type_helper(t.target, polarity, states),
            expand_type_helper(t.argument, polarity, states))
    raise TypeException("Cannot expand type {}".format(t))


def expand_type(ctx: TypingContext, t: Type):
    return expand_type_helper(t, True, [])


def unification(ctx: TypingContext,
                t1: Type,
                t2: Type,
                level: int = 0) -> Type:
    debug = None
    level = 1
    while isinstance(t1, TypeAbstraction):
        level += 1
        v = freshVar(t1.name, level)
        if debug == None:
            debug = v
        t1 = substitution_type_in_type(t1.type, v, t1.name)
    while isinstance(t2, TypeAbstraction):
        level += 1
        v = freshVar(t2.name, level)
        t2 = substitution_type_in_type(t2.type, v, t2.name)

    constrain(ctx, t1, t2)
    r = expand_type(ctx, t1)
    print("v:", debug.state.upper_bounds, debug.state.lower_bounds)
    return reduce_type(ctx, r)
