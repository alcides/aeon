from __future__ import annotations

import sys
from typing import Annotated, Any
from typing import Union

from geneticengine.grammar.metahandlers.base import MetaHandlerGenerator
from geneticengine.grammar.metahandlers.vars import VarRange


from sympy.core.numbers import Infinity, NegativeInfinity
from sympy.sets.sets import Interval, EmptySet, FiniteSet
from sympy.simplify.simplify import simplify
from sympy.logic.boolalg import to_dnf

from aeon.core.types import Type
from aeon.core.types import RefinedType
from aeon.synthesis.grammar.bounds import (
    conditional_to_interval,
    flatten_conditions,
    refined_to_sympy_expression,
    sympy_exp_to_bounded_interval,
)
from aeon.synthesis.grammar.utils import (
    aeon_to_gengy_metahandlers,
    aeon_to_python,
)

max_number = sys.maxsize - 1
min_number = -(sys.maxsize - 1)


def replace_tuples_with_lists(structure):
    if isinstance(structure, tuple):
        return [replace_tuples_with_lists(item) for item in structure]
    elif isinstance(structure, list):
        return [replace_tuples_with_lists(item) for item in structure]
    else:
        return structure


def contains_tuples(lst):
    return any(isinstance(item, tuple) for item in lst)


def split_or_intervals(bounded_intervals, name: str, intervals_list=None):
    intervals_list = [] if intervals_list is None else intervals_list
    # if it is a tuple, it is an Or Interval
    if isinstance(bounded_intervals, tuple):
        for b_interval in bounded_intervals:
            intervals_list = split_or_intervals(b_interval, name, intervals_list)
    elif isinstance(bounded_intervals, list):
        if contains_tuples(bounded_intervals):
            for b_interval in bounded_intervals:
                intervals_list = split_or_intervals(b_interval, name, intervals_list)
        else:
            cond = flatten_conditions(bounded_intervals)
            interval = conditional_to_interval(cond, name)
            intervals_list.append(interval)
    return intervals_list


def interval_to_metahandler(interval: Any, base_type: Type) -> MetaHandlerGenerator:
    python_type: type = aeon_to_python[base_type]
    match interval:
        case EmptySet():
            return None
        case FiniteSet():
            values = [python_type(x) for x in interval.args]
            inst = VarRange(values)
            return Annotated[python_type, inst]
        case Interval():
            max_range = (
                max_number if isinstance(interval.sup, Infinity) else python_type(interval.sup)
            )  # or 2 ** 31 - 1
            max_range = max_range - 1 if interval.right_open else max_range

            min_range = (
                min_number if isinstance(interval.inf, NegativeInfinity) else python_type(interval.inf)
            )  # or -2 ** 31
            min_range = min_range + 1 if interval.left_open else min_range

            metahandler_instance = aeon_to_gengy_metahandlers[base_type](min_range, max_range)
            return Annotated[python_type, metahandler_instance]
        case _:
            raise NotImplementedError()


def intervals_to_metahandlers(intervals_list: list, base_type: Type) -> list[MetaHandlerGenerator]:
    return [x for x in [interval_to_metahandler(i, base_type) for i in intervals_list] if x is not None]


def get_metahandler_union(
    metahandler_list: list[MetaHandlerGenerator],
) -> MetaHandlerGenerator | Union[MetaHandlerGenerator]:
    if len(metahandler_list) == 1:
        return metahandler_list[0]
    else:
        return Union[tuple(metahandler_list)]


def refined_type_to_metahandler(ty: RefinedType) -> MetaHandlerGenerator | Union[MetaHandlerGenerator]:
    name, ref = str(ty.name), ty.refinement
    sympy_exp = refined_to_sympy_expression(ref)
    sympy_exp = simplify(sympy_exp)
    sympy_exp = to_dnf(sympy_exp)
    bounded_intervals = sympy_exp_to_bounded_interval(sympy_exp)
    intervals_list = split_or_intervals(bounded_intervals, name)
    metahandler_list = intervals_to_metahandlers(intervals_list, ty.type)

    return get_metahandler_union(metahandler_list)
