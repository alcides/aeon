import sys
import random
import itertools

from aeon.types import BasicType, TypingContext, t_i, t_f, t_b, t_s

from aeon.synthesis.inequalities import *

from sympy import Symbol, to_cnf, And, Or, Interval, FiniteSet, Union
from sympy.core.numbers import Infinity, NegativeInfinity
from sympy.solvers.inequalities import reduce_rational_inequalities

from aeon.typechecker.zed import zed_verify_satisfiability
from aeon.typechecker.substitutions import substitution_expr_in_expr

from multipledispatch import dispatch

# =============================================================================
# Exception in case we are unable to generate a ranged literal
class RangedException(Exception):
    def __init__(self,
                 name,
                 description="",
                 *args,
                 **kwargs):
        super(RangedException, self).__init__(name, description)

# Ranged context
class RangedContext(object):

    Variable = None

    def __init__(self, ctx):
        self.ctx = ctx # Context of the program
        self.evalctx = dict() # Has the values for each variable
        self.intervals = dict() # Has the ranges for each variable
    
    def add_ranged(self, name, ghost_name, condition):
        if name not in self.rangeds:
            self.intervals[name] = condition
        else:
            ranged = self.intervals[name] # Returns a dict
            ranged[ghost_name] = And(condition, ranged[ghost_name])

# =============================================================================
@dispatch(And)
def interval(and_expr):
    return [interval(x) for x in and_expr.args]

# TODO: Put the random choice in another place
@dispatch(Or)
def interval(or_expr):
    return random.choice([interval(x) for x in or_expr.args])

# TODO: Should never happen
@dispatch(Implies)
def interval(implies_expr):
    left = Not(implies_expr.args[0])
    right = implies_expr.args[1]
    return interval(random.choice([left, right]))

# TODO: Fix
@dispatch(Not)
def interval(not_expr):
    return [interval(not_expr)]

@dispatch(object)
def interval(expression):
    return [expression]

# Auxiliaty, TODO: há estrategias mais rapidas
def flatten_conditions(lista):
    if not isinstance(lista, list):
        return [lista]
    
    result = list()

    for x in lista:
        result += flatten_conditions(x)

    return result

# =============================================================================
def ranged_int(rctx: RangedContext, T: BasicType):
    
    translated = list()

    for restriction in rctx.ctx.restrictions:
        restriction = sympy_translate(rctx, restriction)
        restriction = to_cnf(restriction)
        translated.append(restriction)

    for cond in translated:
        cond = interval(cond)
        cond = flatten_conditions(cond)
        
        try:
            intervals = reduce_rational_inequalities([cond], Symbol(RangedContext.Variable), relational=False)
            
            if isinstance(intervals, FiniteSet):
                return intervals.args[0]

            # Is of type Interval
            else:
                if isinstance(intervals, Union):
                    intervals = random.choice(intervals.args)
                minimum, maximum, is_lopen, is_ropen = intervals.args 

                if isinstance(maximum, Infinity):
                    maximum = sys.maxsize
                
                if isinstance(minimum, NegativeInfinity):
                    minimum = -sys.maxsize
                
                if is_lopen:
                    minimum += 1
                
                if is_ropen:
                  maximum -= 1

                # TODO: otimizar
                return random.randint(minimum, maximum)
  
        except Exception as err:
            print("ERROR: {}".format(err))



#
def ranged_double(rctx: RangedContext, T: BasicType):
    translated = list()

    for restriction in rctx.ctx.restrictions:
        restriction = sympy_translate(rctx, restriction)
        restriction = to_cnf(restriction)
        translated.append(restriction)

    for cond in translated:
        
        cond = interval(cond)
        cond = flatten_conditions(cond)
        
        try:
            
            intervals = reduce_rational_inequalities([cond], Symbol(RangedContext.Variable), relational=False)
            
            if isinstance(intervals, FiniteSet):
                return intervals.args[0]

            else:
            
                if isinstance(intervals, Union):
                    intervals = random.choice(intervals.args)
            
                minimum, maximum, is_lopen, is_ropen = intervals.args 

                if isinstance(maximum, Infinity):
                    maximum = sys.maxsize
                
                if isinstance(minimum, NegativeInfinity):
                    minimum = -sys.maxsize
                
                if is_lopen:
                    minimum += 1
                
                if is_ropen:
                  maximum -= 1

                return random.uniform(minimum, maximum)
  
        except Exception as err:
            print("ERROR: {}".format(err))


# TODO: try to implement this later with the rctx
def ranged_boolean(rctx: RangedContext, T: BasicType):
    
    possibilities = [True, False]

    for restriction in rctx.ctx.restrictions:
        # Try by replacing with true
        new_restr = substitution_expr_in_expr(restriction, Literal(True, t_b), RangedContext.Variable)

        if not zed_verify_satisfiability(rctx.ctx, new_restr) and True in possibilities:
            possibilities.remove(True)

        # Try by replacing with false
        new_restr = substitution_expr_in_expr(restriction, Literal(False, t_b), RangedContext.Variable)
        
        if not zed_verify_satisfiability(rctx.ctx, new_restr) and False in possibilities:
            possibilities.remove(False)

    if not possibilities:
        raise RangedException("Restrictions don't allow the synthesis of boolean expression")

    return random.choice(possibilities)


#
def ranged_string(rctx: RangedContext, T: BasicType):
    pass


#
def ranged_var(rctx: RangedContext, T: BasicType):
    pass


# Ranged Dispatcher
def ranged(ctx: TypingContext, T: BasicType, ):

    assert(isinstance(T, BasicType))

    rctx: RangedContext = RangedContext(ctx)

    # If it is an Integer
    if T == t_i:
        return ranged_int(rctx, T)

    # If it is a Double
    elif T == t_f:
        return ranged_double(rctx, T)

    # If it is a Boolean
    elif T == t_b:
        return ranged_boolean(rctx, T)

    # If it is a String
    elif T == t_s:
        return ranged_string(rctx, T)

    # If it is a Var
    else:
        return ranged_var(rctx, T)
