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

from multipledispatch import dispatch


# =============================================================================
# Exception in case we are unable to generate a ranged literal
class RangedException(Exception):
    def __init__(self, name, description="", *args, **kwargs):
        super(RangedException, self).__init__(name, description)


# Ranged context
class RangedContext(object):
    def __init__(self, ctx):
        self.ctx = ctx  # Context of the program
        self.evalctx = dict()  # Has the values for each variable
        self.intervals = dict()  # Has the ranges for each variable

    def add_ranged(self, name, ghost_name, condition):
        if name not in self.rangeds:
            self.intervals[name] = condition
        else:
            ranged = self.intervals[name]  # Returns a dict
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
def ranged_int(rctx: RangedContext, T: BasicType, name: str,
               conds: List[TypedNode]):

    translated = list()

    for restriction in rctx.ctx.restrictions + conds:
        restriction = sympy_translate(rctx, restriction)
        restriction = to_cnf(restriction)
        translated.append(restriction)

    for cond in translated:
        cond = interval(cond)
        cond = flatten_conditions(cond)

        try:
            intervals = reduce_rational_inequalities([cond],
                                                     Symbol(name),
                                                     relational=False)

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

        except PolynomialError as err:
            logging.info("Failed to do ranged analysis due to: {}".format(err))


#
def ranged_double(rctx: RangedContext, T: BasicType, name: str,
                  conds: List[TypedNode]):
    translated = list()

    for restriction in rctx.ctx.restrictions:
        restriction = sympy_translate(rctx, restriction)
        restriction = to_cnf(restriction)
        translated.append(restriction)

    for cond in translated:

        cond = interval(cond)
        cond = flatten_conditions(cond)

        try:

            intervals = reduce_rational_inequalities([cond],
                                                     Symbol(name),
                                                     relational=False)

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

        except PolynomialError as err:
            logging.info("Failed to do ranged analysis due to: {}".format(err))


# TODO: try to implement this later with the rctx
def ranged_boolean(rctx: RangedContext, T: BasicType, name: str,
                   conds: List[TypedNode]):

    possibilities = [True, False]

    for restriction in rctx.ctx.restrictions:

        # Try by replacing with true
        new_restr = substitution_expr_in_expr(restriction, Literal(True, t_b),
                                              name)

        if not zed_verify_satisfiability(rctx.ctx,
                                         new_restr) and True in possibilities:
            possibilities.remove(True)

        # Try by replacing with false
        new_restr = substitution_expr_in_expr(restriction, Literal(False, t_b),
                                              name)

        if not zed_verify_satisfiability(rctx.ctx,
                                         new_restr) and False in possibilities:
            possibilities.remove(False)

    if not possibilities:
        raise RangedException(
            "Restrictions don't allow the synthesis of boolean expression")

    return random.choice(possibilities)


#
def ranged_string(rctx: RangedContext, T: BasicType, name: str,
                  conds: List[TypedNode]):
    pass


# Ranged Dispatcher
def ranged(ctx: TypingContext, T: BasicType, name: str,
           conds: List[TypedNode]):

    assert (isinstance(T, BasicType))

    rctx: RangedContext = RangedContext(ctx)

    # If it is an Integer
    if T == t_i:
        return ranged_int(rctx, T, name, conds)

    # If it is a Double
    elif T == t_f:
        return ranged_double(rctx, T, name, conds)

    # If it is a Boolean
    elif T == t_b:
        return ranged_boolean(rctx, T, name, conds)

    # If it is a String
    elif T == t_s:
        return ranged_string(rctx, T, name, conds)

    else:
        raise RangedException("Type not supported by range analysis")


def try_ranged(ctx, T: RefinedType):
    if not isinstance(T.type, BasicType):
        raise RangedException(
            "Not a basic type. Please flatten nested refinements first")

    v = ranged(ctx, T.type, name=T.name, conds=[T.cond])
    if v is None:
        raise RangedException("Failed to produce range of type {}".format(T))
    return v
