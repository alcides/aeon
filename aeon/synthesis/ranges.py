import sys
import random

from typing import Dict, List, Tuple

from aeon.ast import *
from aeon.types import *

import aeon.interpreter as interpreter 

# =============================================================================
# Exception in case we are unable to generate a ranged literal
class RangedException(Exception):
    def __init__(self,
                 name,
                 description="",
                 *args,
                 **kwargs):
        super(RangedException, self).__init__(name, description)

# Ranged object with all the ranges of the ghost variables
class Ranged(object):

    def __init__(self, name, typee):
        self.name = name
        self.typee = typee
        self.ghosts = dict()

    def with_ranged(self, ghost_name, minimum, maximum):
        # If we do not yet have the ranged on the ghosts
        if ghost_name not in self.ghosts:
            self.ghosts[ghost_name] = (minimum, maximum)
        # Otherwise, replace if these ranges are more restrictive
        else:
            ghost_min, ghost_max = self.ghosts[ghost_name]

            # Replaces with the most restricted type
            ghost_min = max(ghost_min, minimum)
            ghost_max = min(ghost_max, maximum)

            self.ghosts[ghost_name] = (ghost_min, ghost_max)
    
    # String representation
    def __repr__(self):
        return str(self)

    def __str__(self):
        return '{}:{} :: {}'.format(self.name, self.typee, self.ghosts)
    

# Ranged context
class RangedContext(object):

    def __init__(self):
        self.rangeds = dict()
    
    def add_ranged(self, ranged : Ranged):
        if ranged.name not in self.rangeds:
            self.rangeds[ranged.name] = ranged
        else:
            for ghost_name in ranged.ghosts.keys():
                minimum, maximum = ranged.ghosts[ghost_name]
                self.rangeds[ranged.name].with_ranged(ghost_name, minimum, maximum)

# =============================================================================
# This block of code deals with the native operations and returns proper ranges
''' expr1 > expr2 '''
def ranged_gt(rctx, ctx, t_name, cond):

    value = interpreter.run(cond.argument)

    minimum = value + 1
    maximum = sys.maxsize

    return minimum, maximum

''' expr1 < expr2 '''
def ranged_lt(rctx, ctx, t_name, cond):
    
    value = interpreter.run(cond.argument)

    minimum = -sys.maxsize 
    maximum = value - 1

    return minimum, maximum

''' expr1 >= expr2 '''
def ranged_get(rctx, ctx, t_name, cond):
    
    value = interpreter.run(cond.argument)

    minimum = value
    maximum = sys.maxsize

    return minimum, maximum

''' expr1 <= expr2 '''
def ranged_let(rctx, ctx, t_name, cond):
        
    value = interpreter.run(cond.argument)

    minimum = -sys.maxsize 
    maximum = value

    return minimum, maximum

''' expr1 == expr2 '''
def ranged_eq(rctx, ctx, t_name, cond):
    print(">>", type(cond.argument))
    value = interpreter.run(cond.argument)

    minimum = value 
    maximum = value 

    return minimum, maximum

# #TODO: Special operations, need to work with both boolean conditions and expressions
''' cond1 && cond2 '''
def ranged_and(rctx, ctx, t_name, cond):

    left = cond.target.argument
    right = cond.argument

    ranged_dispatcher(rctx, ctx, t_name, left) 
    ranged_dispatcher(rctx, ctx, t_name, right)


''' cond1 || cond2 '''
def ranged_or(rctx, ctx, t_name, cond):
    
    left = cond.target.argument
    right = cond.argument

    if random.random() < 0.5:
        ranged_dispatcher(rctx, ctx, t_name, left) 
    else:
        ranged_dispatcher(rctx, ctx, t_name, right)


''' cond1 --> cond2 ~> !cond1 || cond2'''
def ranged_implie(rctx, ctx, t_name, cond):
    print("TODOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOO")
    pass


# Dispatchr
def ranged_dispatcher(rctx, ctx, t_name, cond):

    assert(isinstance(cond, Application))

    target = cond.target
    argument = cond.argument

    # Any of the other operations
    if isinstance(target.target, TApplication):
        name = target.target.target.name

        if name == '>':
            minimum, maximum = ranged_gt(rctx, ctx, name, cond)
        elif name == '<':
            minimum, maximum = ranged_lt(rctx, ctx, name, cond)
        elif name == '>=':
            minimum, maximum = ranged_get(rctx, ctx, name, cond)
        elif name == '<=':
            minimum, maximum = ranged_let(rctx, ctx, name, cond)
        elif name == '==':
            minimum, maximum = ranged_eq(rctx, ctx, name, cond)
        else:
            raise RangedException("Unknown operator when dispatching ranged".format(name))

        # Obtain the ghost_name for the type
        left = cond.target.argument
        ghost_name = '_native' if isinstance(left, Var) else left.target.name.split('_')[2]

        ranged = Ranged(t_name, ctx.variables[t_name])
        ranged.with_ranged(ghost_name, minimum, maximum)

        rctx.add_ranged(ranged)

    # If it is an -->, || or &&
    else:
        name = target.target.name

        if name == '-->':
            ranged_implie(rctx, ctx, t_name, cond)

        elif name == '||':
            ranged_or(rctx, ctx, t_name, cond)

        elif name == '&&':
            ranged_and(rctx, ctx, t_name, cond)

        else:
            raise RangedException("Unknown operator when dispatching ranged".format(name))

# =============================================================================
'''
    x : Int | x > 0                     ~~> ] 0, maxint [
    x : Int | x > 0 && y < 30           ~~> ] 0, maxint [
    x : Int | x > 0 && x < 10           ~~> ] 0, maxint [ AND ] minint, 10 [
    x : Int | !(x > 0 && x < 10)        ~~> [ 10, maxint [ OR ] minint, 0 ] (inverter os valores)
    x : Int | !(x < 0 || x > 10)        ~~> ] minint, 10 [ AND ] 0, maxint [ (inverter os valores)
    x : Int | x >= 0 || x < 0           ~~> [ 0, maxint [ OR ] minint, 0 [
    x : Int | x == 0                    ~~> [ 0, 0 ]
    x : Int | f(x) > 0                  ~~> ] minint, maxint [
    x : Int | x < list.size             ~~> ] minint, interpretar(list.size) [
    x : Int | y == 1 && x > y           ~~> ] 1, maxint [
    x : Int | y > 1 && x > y            ~~> ] 2, maxint [
'''
def ranged_int(rctx: RangedContext, ctx: TypingContext, T: BasicType):

    maximum = sys.maxsize
    minimum = -sys.maxsize

    # Put variable the variable we want on the right side
    # TODO: This is bad, temporary 
    variable = list(ctx.variables.keys())[-1]

    # Set the initial ranged
    ranged = Ranged(variable, t_i)
    ranged.with_ranged('_native', minimum, maximum)
    rctx.add_ranged(ranged)

    for restriction in ctx.restrictions:    
        ranged_dispatcher(rctx, ctx, variable, restriction)

    ranged = rctx.rangeds[variable]
    minimum, maximum = ranged.ghosts['_native']

    value = random.randint(minimum, maximum)

    print("RangedContext:", ranged)
    print("Value:", value)
    return value        


def ranged_double(rctx: RangedContext, ctx: TypingContext, T: BasicType):

    maximum = sys.maxsize
    minimum = -sys.maxsize

    # Put variable the variable we want on the right side
    # TODO: This is bad, temporary 
    variable = list(ctx.variables.keys())[-1]

    # Set the initial ranged
    ranged = Ranged(variable, ctx.variables[variable])
    ranged.with_ranged('_native', minimum, maximum)
    rctx.add_ranged(ranged)

    for restriction in ctx.restrictions:    
        ranged_dispatcher(rctx, ctx, variable, restriction)

    ranged = rctx.rangeds[variable]
    minimum, maximum = ranged.ghosts['_native']

    value = random.randint(minimum, maximum)

    return value        


def ranged_boolean(rctx: RangedContext, ctx: TypingContext, T: BasicType):
    
    maximum = 1
    minimum = 0

    # Put variable the variable we want on the right side
    # TODO: This is bad, temporary 
    variable = list(ctx.variables.keys())[-1]

    # Set the initial ranged
    ranged = Ranged(variable, ctx.variables[variable])
    ranged.with_ranged('_native', minimum, maximum)
    rctx.add_ranged(ranged)

    for restriction in ctx.restrictions:    
        ranged_dispatcher(rctx, ctx, variable, restriction)

    ranged = rctx.rangeds[variable]
    minimum, maximum = ranged.ghosts['_native']

    value = random.randint(minimum, maximum)

    return bool(value)       


def ranged_string(rctx: RangedContext, ctx: TypingContext, T: BasicType):
    value = None
    return value


# TODO:
def ranged_var(rctx: RangedContext, ctx: TypingContext, T: BasicType):
    pass


def ranged(ctx: TypingContext, T: BasicType):

    assert(isinstance(T, BasicType))

    rctx: RangedContext = RangedContext()

    # Obtain the restrictions
    #restrictions = ctx.restrictions

    # Filter the non-restricted refinements from the code
    #restrictions = filter_non_restricted(restrictions)

    # If it is an Integer
    if T == t_i:
        return ranged_int(rctx, ctx, T)

    # If it is a Double
    elif T == t_f:
        return ranged_double(rctx, ctx, T)

    # If it is a Boolean
    elif T == t_b:
        return ranged_boolean(rctx, ctx, T)

    # If it is a String
    elif T == t_s:
        return ranged_string(rctx, ctx, T)

    # If it is a Var
    else:
        return ranged_var(rctx, ctx, T)
