from __future__ import annotations

import sys
from abc import ABC
from dataclasses import make_dataclass
from typing import Optional, Tuple, Protocol
from typing import Type as TypingType

from geneticengine.grammar.metahandlers.base import MetaHandlerGenerator
from geneticengine.prelude import abstract

from aeon.core.liquid import LiquidApp, LiquidTerm
from aeon.core.substitutions import substitution_in_type
from aeon.core.terms import Abstraction, Application, Literal
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, Type
from aeon.core.types import BaseType
from aeon.core.types import Bottom
from aeon.core.types import RefinedType
from aeon.core.types import Top
from aeon.core.types import t_bool
from aeon.core.types import t_float
from aeon.core.types import t_int
from aeon.core.types import t_string
from aeon.decorators import Metadata
from aeon.synthesis_grammar.mangling import mangle_term, mangle_type
from aeon.synthesis_grammar.utils import (
    aeon_prelude_ops_to_text,
    prelude_ops,
)
from aeon.typechecking.context import TypingContext

max_number = sys.maxsize - 1
min_number = -(sys.maxsize - 1)


# def extract_class_name(class_name: str) -> str:
#     prefixes = ["var_", "app_", "refined_app_", "refined_var_", "literal_Refined_", "literal_"]
#     for prefix in prefixes:
#         if class_name.startswith(prefix):
#             return class_name[len(prefix) :]
#     return class_name


class GrammarError(Exception):
    pass


# Protocol for classes that can have a get_core method
class HasGetCore(Protocol):

    def get_core(self): ...


classType = TypingType[HasGetCore]


# def mk_method_core(cls: classType) -> classType:

#     def get_core(self):
#         class_name = self.__class__.__name__
#         # the prefix is either "var_", "app_", "refined_app" or "refined_var"
#         class_name_without_prefix = extract_class_name(class_name)

#         if class_name_without_prefix in text_to_aeon_prelude_ops.keys():
#             op = text_to_aeon_prelude_ops.get(class_name_without_prefix)
#             var_values = []
#             base = Var(op)
#             for attr_name, _ in cls.__annotations__.items():
#                 value = getattr(self, attr_name, None)
#                 base = Application(base, value.get_core())
#                 var_values.append(value)

#             assert len(var_values) == 2
#         elif class_name.startswith("If"):
#             if_dict = {}
#             for attr_name, ty in cls.__annotations__.items():
#                 value = getattr(self, attr_name, None)
#                 # aeon_type = ty.__name__[2:]
#                 if_dict[attr_name] = value.get_core()
#                 # if_dict[attr_name] = Annotation(value.get_core(), BaseType(aeon_type))

#             base = If(if_dict["cond"], if_dict["then"], if_dict["otherwise"])

#         else:
#             base = Var(class_name_without_prefix)
#             for attr_name, _ in cls.__annotations__.items():
#                 value = getattr(self, attr_name, None)

#                 base = Application(base, value.get_core())

#         return base

#     setattr(cls, "get_core", get_core)
#     return cls


def mk_method_core_literal(cls: classType, ty: Type) -> classType:

    def get_core(self):
        value = getattr(self, "value", None)
        return Literal(value, type=ty)

    setattr(cls, "get_core", get_core)
    return cls


def liquid_term_to_str(ty: RefinedType) -> str:
    var: str = ty.name
    base_type_str: str = ty.type.name
    refinement: LiquidTerm = ty.refinement
    if isinstance(refinement, LiquidApp):
        refined_type_str = (
            str(ty.refinement).replace(var, base_type_str).replace("(", "").replace(")", "").replace(" ", "_")
        )
        for op, op_str in aeon_prelude_ops_to_text.items():
            refined_type_str = refined_type_str.replace(op, op_str)
    else:
        assert False
    return refined_type_str


# def process_type_name(ty: Type) -> str:
#     if isinstance(ty, RefinedType):
#         refinement_str = liquid_term_to_str(ty)
#         refined_type_name = f"Refined_{refinement_str}"
#         return refined_type_name

#     elif isinstance(ty, Top) or isinstance(ty, Bottom):
#         return str(ty)
#     elif isinstance(ty, BaseType):
#         return str(ty.name)
#     else:
#         assert False


# def replace_tuples_with_lists(structure):
#     if isinstance(structure, tuple):
#         return [replace_tuples_with_lists(item) for item in structure]
#     elif isinstance(structure, list):
#         return [replace_tuples_with_lists(item) for item in structure]
#     else:
#         return structure


# def contains_tuples(lst):
#     return any(isinstance(item, tuple) for item in lst)


# def split_or_intervals(bounded_intervals, name, intervals_list=None):
#     intervals_list = [] if intervals_list is None else intervals_list
#     # if it is a tuple, it is an Or Interval
#     if isinstance(bounded_intervals, tuple):
#         for b_interval in bounded_intervals:
#             intervals_list = split_or_intervals(b_interval, name, intervals_list)
#     elif isinstance(bounded_intervals, list):
#         if contains_tuples(bounded_intervals):
#             for b_interval in bounded_intervals:
#                 intervals_list = split_or_intervals(b_interval, name, intervals_list)
#         else:
#             cond = flatten_conditions(bounded_intervals)
#             interval = conditional_to_interval(cond, name)
#             intervals_list.append(interval)
#     return intervals_list


# def intervals_to_metahandlers(
#     gengy_metahandler: Any, intervals_list: list, base_type_str: str, ref: LiquidTerm
# ) -> list[MetaHandlerGenerator]:
#     metahandler_list: list[MetaHandlerGenerator] = []
#     python_type: type = aeon_to_python_types[base_type_str]
#     for interval in intervals_list:
#         if isinstance(interval, Interval):
#             if isinstance(ref, LiquidApp):
#                 max_range = max_number if isinstance(interval.sup, Infinity) else interval.sup  # or 2 ** 31 - 1
#                 max_range = max_range - 1 if interval.right_open else max_range

#                 min_range = min_number if isinstance(interval.inf, NegativeInfinity) else interval.inf  # or -2 ** 31
#                 min_range = min_range + 1 if interval.left_open else min_range

#                 metahandler_instance = gengy_metahandler(min_range, max_range)
#                 metahandler_type = Annotated[python_type, metahandler_instance]  # type: ignore
#                 metahandler_list.append(metahandler_type)
#             else:
#                 assert False
#         elif isinstance(interval, EmptySet):
#             pass
#         else:
#             assert False
#     return metahandler_list


# def get_metahandler_union(
#     metahandler_list: list[MetaHandlerGenerator],
# ) -> MetaHandlerGenerator | Union[MetaHandlerGenerator]:
#     if len(metahandler_list) == 1:
#         return metahandler_list[0]
#     else:
#         return Union[tuple(metahandler_list)]


# def refined_type_to_metahandler(ty: RefinedType) -> MetaHandlerGenerator | Union[MetaHandlerGenerator]:
#     base_type_str = str(ty.type.name)
#     gengy_metahandler = aeon_to_gengy_metahandlers[base_type_str]
#     name, ref = ty.name, ty.refinement

#     sympy_exp = refined_to_sympy_expression(ref)
#     sympy_exp = simplify(sympy_exp)
#     sympy_exp = to_dnf(sympy_exp)
#     bounded_intervals = sympy_exp_to_bounded_interval(sympy_exp)
#     intervals_list = split_or_intervals(bounded_intervals, name)
#     metahandler_list = intervals_to_metahandlers(gengy_metahandler, intervals_list, base_type_str, ref)

#     return get_metahandler_union(metahandler_list)


# def handle_refined_type(class_name: str, ty: RefinedType, grammar_nodes: list[type]) -> tuple[list[type], type]:
#     """Handle the creation of classes for refined types and update grammar nodes accordingly."""
#     class_name = "t_" + class_name if not class_name.startswith("t_") else class_name
#     new_abs_class = create_abstract_class(class_name)
#     grammar_nodes.append(new_abs_class)

#     metahandler_type = refined_type_to_metahandler(ty)
#     new_class = create_literal_class(class_name[2:], metahandler_type, new_abs_class)
#     grammar_nodes.append(new_class)

#     base_type_name = process_type_name(ty.type)
#     grammar_nodes, _ = find_class_by_name(base_type_name, grammar_nodes)

#     return grammar_nodes, new_abs_class


def is_valid_class_name(class_name: str) -> bool:
    return class_name not in prelude_ops and not class_name.startswith(("_anf_", "target"))


# def create_if_class(class_name: str, parent_class_name: str, grammar_nodes: list[type]) -> list[type]:
#     grammar_nodes, cond_class = find_class_by_name("Bool", grammar_nodes)
#     grammar_nodes, parent_class = find_class_by_name(parent_class_name, grammar_nodes)

#     fields = [("cond", cond_class), ("then", parent_class), ("otherwise", parent_class)]

#     if_class = create_new_class(class_name, parent_class, fields)
#     grammar_nodes.append(if_class)

#     return grammar_nodes


# def build_control_flow_grammar_nodes(grammar_nodes: list[type]) -> list[type]:
#     types_names_set = {
#         cls.__name__
#         for cls in grammar_nodes
#         if cls.__base__ is ABC and not any(issubclass(cls, other) and cls is not other for other in grammar_nodes)
#     }
#     for ty_name in types_names_set:
#         grammar_nodes = create_if_class(f"If_{ty_name}", ty_name, grammar_nodes)
#     return grammar_nodes


ae_top = type("ae_top", (ABC,), {})


def extract_all_types(types: list[Type]) -> dict[Type, TypingType]:
    data: dict[Type, TypingType] = {Top(): ae_top}
    for ty in types:
        class_name = mangle_type(ty)
        match ty:
            case BaseType(_):
                ty_abstract_class = type(class_name, (ae_top,), {})
                ty_abstract_class = abstract(ty_abstract_class)
                data[ty] = ty_abstract_class
            case RefinedType(_, itype, _):
                data.update(extract_all_types([itype]))
                parent = data[itype]
                ty_abstract_class = type(class_name, (parent,), {})
                ty_abstract_class = abstract(ty_abstract_class)
                data[ty] = ty_abstract_class
            case AbstractionType(var_name, var_type, return_type):
                data.update(extract_all_types([var_type, substitution_in_type(return_type, Var("__self__"), var_name)]))
                ty_abstract_class = type(class_name, (ae_top,), {})
                ty_abstract_class = abstract(ty_abstract_class)
                data[ty] = ty_abstract_class
            case Top():
                data[ty] = ae_top
            case Bottom():
                pass
            case _:
                print(ty)
                assert False
    return data


aeon_to_python: dict[Type, TypingType] = {
    t_bool: bool,
    t_int: int,
    t_string: str,
    t_float: float,
}


def create_literal_class(
    aeon_type: Type, parent_class: type, value_type: None | type | MetaHandlerGenerator = None
) -> type:
    """Create and return a new literal class with the given name and value type, based on the provided abstract class."""
    if value_type is None:
        value_type = aeon_to_python[aeon_type]

    class_name = mangle_type(aeon_type)
    new_class = make_dataclass(
        f"literal_{class_name}",
        [("value", value_type)],
        bases=(parent_class,),
    )
    return mk_method_core_literal(new_class, aeon_type)


def create_literals_nodes(type_info: dict[Type, TypingType], types: Optional[list[Type]] = None) -> list[TypingType]:
    """Creates all literal nodes for known types with literals (bool, int, float, string)"""
    if types is None:
        types = [t_bool, t_int, t_float, t_string]
    return [create_literal_class(aeon_ty, type_info[aeon_ty]) for aeon_ty in types]


def create_var_node(name: str, ty: Type, python_ty: TypingType) -> TypingType:
    """Creates a python type for a given variable in context."""
    vname = mangle_term(name)
    dc = make_dataclass(f"var_{vname}", [], bases=(python_ty,))

    def get_core(_self):
        return Var(name)

    setattr(dc, "get_core", get_core)
    return dc


def create_var_nodes(vars: list[Tuple[str, Type]], type_info: dict[Type, TypingType]) -> list[TypingType]:
    """Creates a list of python types for all variables in context."""
    return [create_var_node(var_name, ty, type_info[ty]) for (var_name, ty) in vars]


def create_abstraction_node(ty: AbstractionType, type_info: dict[Type, TypingType]) -> TypingType:
    """Creates a dataclass to represent an abstraction (\\_0 -> x) of type sth_arrow_X."""
    vname = f"lambda_{mangle_type(ty)}"
    dc = make_dataclass(vname, [("body", type_info[ty.type])], bases=(type_info[ty],))

    def get_core(_self):
        return Abstraction("_0", _self.body.get_core())

    # Note: We cannot use the variable inside Abstraction.
    setattr(dc, "get_core", get_core)
    return dc


def create_abstraction_nodes(type_info: dict[Type, TypingType]) -> list[TypingType]:
    return [create_abstraction_node(ty, type_info) for ty in type_info if isinstance(ty, AbstractionType)]


def create_application_node(ty: AbstractionType, type_info: dict[Type, TypingType]) -> TypingType:
    """Creates a dataclass to represent an abstraction (\\_0 -> x) of type sth_arrow_X."""
    vname = f"app_{mangle_type(ty)}"
    dc = make_dataclass(vname, [("fun", type_info[ty]), ("arg", type_info[ty.var_type])], bases=(type_info[ty.type],))
    # Note: this would require dependent type dynamic processing on the return type (parent class)

    def get_core(_self):
        return Application(_self.fun.get_core(), _self.arg.get_core())

    setattr(dc, "get_core", get_core)
    return dc


def create_application_nodes(type_info: dict[Type, TypingType]) -> list[TypingType]:
    return [create_application_node(ty, type_info) for ty in type_info if isinstance(ty, AbstractionType)]


def gen_grammar_nodes(
    ctx: TypingContext,
    synth_fun_type,
    synth_func_name: str,
    metadata: Metadata,
    grammar_nodes: list[type] | None = None,
) -> tuple[list[type], type]:
    """Generate grammar nodes from the variables in the given TypingContext.

    This function iterates over the variables in the provided TypingContext. For each variable,
    it generates a new class using the create_class_from_ctx_var function and adds it to
    the list of grammar_nodes. If no initial list of grammar_nodes is provided, it starts with an empty list.

    Args:
        ctx (TypingContext): The TypingContext to extract variables from.
        synth_func_name (str) : The name of the function where the hole is located
        metadata (Metadata): The metadata of the program.
        grammar_nodes (list[type]): Initial list of grammar nodes. Defaults to an empty list.

    Returns:
        list[type]: The list of generated grammar nodes.
    """
    if grammar_nodes is None:
        grammar_nodes = []

    current_metadata = metadata.get(synth_func_name, {})
    is_recursion_allowed = current_metadata.get("recursion", False)
    vars_to_ignore = current_metadata.get("hide", [])

    def skip(name: str) -> bool:
        if name == synth_func_name:
            return not is_recursion_allowed
        elif name in vars_to_ignore:
            return True
        elif name.startswith("__internal__"):
            return True
        elif name in ["native", "native_import", "print"]:
            return True
        else:
            return False

    ctx_vars = [(var_name, ty) for (var_name, ty) in ctx.vars() if not skip(var_name)]

    type_nodes = extract_all_types([t_bool, t_float, t_int, t_string] + [x[1] for x in ctx_vars] + [synth_fun_type])

    literals = create_literals_nodes(type_nodes)
    vars = create_var_nodes(ctx_vars, type_nodes)
    abstractions = create_abstraction_nodes(type_nodes)
    applications = create_application_nodes(type_nodes)

    ret = list(type_nodes.values()) + literals + vars + abstractions + applications
    return ret, type_nodes[synth_fun_type]


def print_grammar_nodes_names(grammar_nodes: list[type]) -> None:
    class_names = [cls.__name__ for cls in grammar_nodes]
    print(class_names)


def print_grammar_nodes(grammar_nodes: list[type]) -> None:
    for cls in grammar_nodes:
        parents = [base.__name__ for base in cls.__bases__]
        print("@dataclass")
        print(f"class {cls.__name__}({''.join(parents)}):")
        class_vars = cls.__annotations__
        if class_vars:
            for var_name, var_type in class_vars.items():
                print(f"\t {var_name}: {var_type.__name__}")
        else:
            print("\t pass")
        print()
        # print("---------------------------------------------------")
