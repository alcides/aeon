import sys
import random
import itertools
import logging

from typing import List

from aeon.types import BasicType, RefinedType, TypingContext, t_i, t_f, t_b, t_s
from aeon.ast import TypedNode

from aeon.synthesis.inequalities import *

from sympy import Symbol, to_cnf, And, Or, Interval, FiniteSet, Union
from sympy.core.numbers import Infinity, NegativeInfinity
from sympy.solvers.inequalities import reduce_rational_inequalities
from sympy.polys.polyerrors import PolynomialError

from aeon.typechecker.zed import zed_verify_satisfiability
from aeon.typechecker.substitutions import substitution_expr_in_expr

from functools import lru_cache
from multipledispatch import dispatch

from aeon.synthesis.utils import flatten_refined_type


# =============================================================================
# Exception in case we are unable to generate a ranged literal
class RangedException(Exception):
    def __init__(self, name, description="", *args, **kwargs):
        super(RangedException, self).__init__(name, description)


# Ranged context
class RangedContext(object):
    def __init__(self, ctx):
        '''
            e.g.
            {
                'w': {'_native': [0, 10]},
                'x': {'_native': [[0.0, 10.5], [11.3, 22.1]]},
                'y': {'_native': [True, False]},
                'z': {'size': [3, 10]},
                'k': {'name': {size: [4, 4]}, 'age':[0, 100]},
            }
        '''
        self.ctx = ctx
        self.intervals = dict()  # Has the ranges for each variable

    def add_ranged(self, name, ghost_name, interval):
        if name not in self.rangeds:
            self.intervals[name] = dict()
            self.intervals[name][ghost_name] = interval
        else:
            ranged = self.intervals[name]  # Returns a dict
            ranged[ghost_name] = ranged[ghost_name].union(interval)
    
    def get_ranged(self, name, ghost_name):
        return self.intervals[name][ghost_name]


# =============================================================================
@dispatch(And)
def interval(and_expr):
    return [interval(x) for x in and_expr.args]


# TODO: Put the random choice in another place
@dispatch(Or)
def interval(or_expr):
    return random.choice([interval(x) for x in or_expr.args])


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
# Generate a random restricted int
def ranged_int(rctx: RangedContext, name: str):
    
    intervals = rctx.get_ranged(name, '_native')

    if isinstance(intervals, FiniteSet):
        return intervals.args[0]

    elif isinstance(intervals, Union):
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
    
# Generate a random restricted double
def ranged_double(rctx: RangedContext, name: str):
    pass

# Generate a random restricted boolean
def ranged_boolean(rctx: RangedContext, name: str):

    possibilities = [True, False]

    for restriction in rctx.ctx.restrictions:
        for poss in possibilities:
            # Try by replacing with true
            new_restr = substitution_expr_in_expr(restriction, Literal(poss, t_b),
                                                name)

            if not zed_verify_satisfiability(rctx.ctx,
                                            new_restr) and poss in possibilities:
                possibilities.remove(poss)

    if not possibilities:
        raise RangedException(
            "Restrictions don't allow the synthesis of boolean expression")

    return random.choice(possibilities)


# Generate a random restricted string
def ranged_string(rctx: RangedContext, name: str):
    pass

# =============================================================================
# TODO: Only works with native types \ {Strings}, and with the name, name
@lru_cache
def generate_ranged_context(ctx, name, T, conds):

    translated = list()

    rctx = RangedContext(ctx)

    restrictions = ctx.restrictions + conds

    for restriction in restrictions:
        restriction = sympy_translate(rctx, restriction)
        restriction = to_cnf(restriction)
        translated.append(restriction)
    
    for cond in translated:
        cond = interval(cond)
        cond = flatten_conditions(cond)

        try:
            interval = reduce_rational_inequalities([cond],
                                                     Symbol(name),
                                                     relational=False)
            
            restriction.add_ranged(name, '_native', interval)

        except PolynomialError as err:
            logging.info("Failed to do ranged analysis due to: {}".format(err))

    return rctx


# =============================================================================
# Ranged Dispatcher
def ranged(ctx: TypingContext, T: BasicType, name: str,
           conds: List[TypedNode]):

    switcher = {
        t_i : ranged_int,
        t_f : ranged_double,
        t_b : ranged_boolean,
        t_s : ranged_string
    }

    rctx = generate_ranged_context(ctx, name, T, conds)
    ranged_option = switcher.get(T)

    if not ranged_option:
        raise RangedException("Type not supported by range analysis")

    return ranged_option(rctx, name)

# =============================================================================
def try_ranged(ctx, T: RefinedType):

    if not isinstance(T.type, BasicType):
        T = flatten_refined_type(T)

    value = ranged(ctx, name = T.name, T.type, conds=[T.cond])
    
    if not value:
        raise RangedException("Failed to produce range of type {}".format(T))
    
    return value
