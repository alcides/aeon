from typing import List, Callable
from functools import reduce
from aeon.types import TypeException, Type, TypingContext, BasicType, AbstractionType, TypeAbstraction, \
    IntersectionType, SumType, TypeApplication, RefinedType, top, bottom
from aeon.typechecker.substitutions import substitution_type_in_type
from aeon.typechecker.type_simplifier import reduce_type


class VariableState(object):
    def __init__(self):
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
        return "var({} l={} u={})".format(self.original_name, self.state.lower_bounds, self.state.upper_bounds)


def freshVar(name: str) -> Variable:
    return Variable(name, VariableState())


def constrain(ctx: TypingContext, t1: Type, t2: Type):
    if isinstance(t1, BasicType) and isinstance(t2, BasicType) and t1 == t2:
        pass
    elif isinstance(t1, AbstractionType) and isinstance(t2, AbstractionType):
        constrain(ctx, t2.arg_type, t1.arg_type)
        constrain(ctx, t1.return_type, t2.return_type)
    elif isinstance(t1, Variable) and isinstance(t2, Variable):
        t1.state.upper_bounds.append(t2)
        t2.state.lower_bounds.append(t1)
    elif isinstance(t1, Variable):
        t1.state.upper_bounds.append(t2)
        for t in t1.state.lower_bounds:
            constrain(ctx, t, t2)
    elif isinstance(t2, Variable):
        t2.state.lower_bounds.append(t1)
        for t in t2.state.upper_bounds:
            constrain(ctx, t1, t)
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


def collapse(t: Variable, explored: List[Variable], polarity : bool):
    if polarity:
        r : Type = top
        if str(t.original_name) not in explored:
            for high in t.state.upper_bounds:
                if isinstance(high, Variable):
                    high = collapse(high, explored + [str(t.original_name)], not polarity)
                r = IntersectionType(r, high)
    else:
        r : Type = bottom
        if str(t.original_name) not in explored:
            for low in t.state.lower_bounds:
                if isinstance(low, Variable):
                    low = collapse(low, explored + [str(t.original_name)], not polarity)
                r = SumType(r, low)
    print("red", r, explored)
    #r = reduce_type(None, r)
    return r


def unification(ctx: TypingContext,
                t1: Type,
                t2: Type) -> Type:
    type_variables = []
    original_t1 = t1
    while isinstance(t1, TypeAbstraction):
        v = freshVar(t1.name)
        type_variables.append(v)
        t1 = substitution_type_in_type(t1.type, v, t1.name)
    while isinstance(t2, TypeAbstraction):
        v = freshVar(t2.name)
        t2 = substitution_type_in_type(t2.type, v, t2.name)

    constrain(ctx, t1, t2)
    #r = expand_type(ctx, t1)
    #print("red:", reduce_type(None, r))
    l = [ collapse(t, [], True) for t in type_variables ]
    r = reduce( lambda x, y: TypeApplication(x, y), l, original_t1 )
    print("result:", r)
    return r
