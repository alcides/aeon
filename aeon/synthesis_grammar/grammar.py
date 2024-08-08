from __future__ import annotations

import sys
from abc import ABC
from dataclasses import make_dataclass
from typing import Annotated, Union, Protocol, Any
from typing import Type as TypingType

from geneticengine.grammar.metahandlers.base import MetaHandlerGenerator
from lark.lexer import Token
from sympy.core.numbers import Infinity, NegativeInfinity
from sympy.logic.boolalg import to_dnf
from sympy.sets.sets import Interval, EmptySet
from sympy.simplify.simplify import simplify

from aeon.core.liquid import LiquidApp, LiquidTerm
from aeon.core.terms import Application
from aeon.core.terms import If
from aeon.core.terms import Literal
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
from aeon.synthesis_grammar.bounds import (
    refined_to_sympy_expression,
    sympy_exp_to_bounded_interval,
    conditional_to_interval,
    flatten_conditions,
)
from aeon.synthesis_grammar.utils import (
    text_to_aeon_prelude_ops,
    aeon_prelude_ops_to_text,
    aeon_to_python_types,
    aeon_to_gengy_metahandlers,
    prelude_ops,
)
from aeon.typechecking.context import TypingContext

max_number = sys.maxsize - 1
min_number = -(sys.maxsize - 1)


def extract_class_name(class_name: str) -> str:
    prefixes = [
        "var_", "app_", "refined_app_", "refined_var_", "literal_Refined_",
        "literal_"
    ]
    for prefix in prefixes:
        if class_name.startswith(prefix):
            return class_name[len(prefix):]
    return class_name


class GrammarError(Exception):
    pass


# Protocol for classes that can have a get_core method
class HasGetCore(Protocol):

    def get_core(self):
        ...


classType = TypingType[HasGetCore]


def mk_method_core(cls: classType) -> classType:

    def get_core(self):
        class_name = self.__class__.__name__
        # the prefix is either "var_", "app_", "refined_app" or "refined_var"
        class_name_without_prefix = extract_class_name(class_name)

        if class_name_without_prefix in text_to_aeon_prelude_ops.keys():
            op = text_to_aeon_prelude_ops.get(class_name_without_prefix)
            var_values = []
            base = Var(op)
            for attr_name, _ in cls.__annotations__.items():
                value = getattr(self, attr_name, None)
                base = Application(base, value.get_core())
                var_values.append(value)

            assert len(var_values) == 2
        elif class_name.startswith("If"):
            if_dict = {}
            for attr_name, ty in cls.__annotations__.items():
                value = getattr(self, attr_name, None)
                # aeon_type = ty.__name__[2:]
                if_dict[attr_name] = value.get_core()
                # if_dict[attr_name] = Annotation(value.get_core(), BaseType(aeon_type))

            base = If(if_dict["cond"], if_dict["then"], if_dict["otherwise"])

        else:
            base = Var(class_name_without_prefix)
            for attr_name, _ in cls.__annotations__.items():
                value = getattr(self, attr_name, None)

                base = Application(base, value.get_core())

        return base

    setattr(cls, "get_core", get_core)
    return cls


def mk_method_core_literal(cls: classType) -> classType:

    def get_core(self):
        class_name = self.__class__.__name__
        class_name_without_prefix = extract_class_name(class_name)
        value = getattr(self, "value", None)
        try:
            if value is not None:
                if class_name_without_prefix == "Int" or class_name_without_prefix.startswith(
                        "Int"):
                    base = Literal(int(value), type=t_int)
                elif class_name_without_prefix == "Float" or class_name_without_prefix.startswith(
                        "Float"):
                    base = Literal(float(value), type=t_float)
                elif class_name_without_prefix == "Bool" or class_name_without_prefix.startswith(
                        "Bool"):
                    value = str(value) == "true"
                    base = Literal(value, type=t_bool)
                elif class_name_without_prefix == "String" or class_name_without_prefix.startswith(
                        "String"):
                    v = str(value)[1:-1]
                    base = Literal(str(v), type=t_string)
                else:
                    assert False

                return base
        except Exception as e:
            raise GrammarError("no value\n ", e)

    setattr(cls, "get_core", get_core)
    return cls


def liquid_term_to_str(ty: RefinedType) -> str:
    var: str = ty.name
    base_type_str: str = ty.type.name
    refinement: LiquidTerm = ty.refinement
    if isinstance(refinement, LiquidApp):
        refined_type_str = (str(ty.refinement).replace(
            var, base_type_str).replace("(", "").replace(")",
                                                         "").replace(" ", "_"))
        for op, op_str in aeon_prelude_ops_to_text.items():
            refined_type_str = refined_type_str.replace(op, op_str)
    else:
        assert False
    return refined_type_str


def process_type_name(ty: Type) -> str:
    if isinstance(ty, RefinedType):
        refinement_str = liquid_term_to_str(ty)
        refined_type_name = f"Refined_{refinement_str}"
        return refined_type_name

    elif isinstance(ty, Top) or isinstance(ty, Bottom):
        return str(ty)
    elif isinstance(ty, BaseType):
        return str(ty.name)
    else:
        assert False


def replace_tuples_with_lists(structure):
    if isinstance(structure, tuple):
        return [replace_tuples_with_lists(item) for item in structure]
    elif isinstance(structure, list):
        return [replace_tuples_with_lists(item) for item in structure]
    else:
        return structure


def contains_tuples(lst):
    return any(isinstance(item, tuple) for item in lst)


def split_or_intervals(bounded_intervals, name, intervals_list=None):
    intervals_list = [] if intervals_list is None else intervals_list
    # if it is a tuple, it is an Or Interval
    if isinstance(bounded_intervals, tuple):
        for b_interval in bounded_intervals:
            intervals_list = split_or_intervals(b_interval, name,
                                                intervals_list)
    elif isinstance(bounded_intervals, list):
        if contains_tuples(bounded_intervals):
            for b_interval in bounded_intervals:
                intervals_list = split_or_intervals(b_interval, name,
                                                    intervals_list)
        else:
            cond = flatten_conditions(bounded_intervals)
            interval = conditional_to_interval(cond, name)
            intervals_list.append(interval)
    return intervals_list


def intervals_to_metahandlers(gengy_metahandler: Any, intervals_list: list,
                              base_type_str: str,
                              ref: LiquidTerm) -> list[MetaHandlerGenerator]:
    metahandler_list: list[MetaHandlerGenerator] = []
    python_type: type = aeon_to_python_types[base_type_str]
    for interval in intervals_list:
        if isinstance(interval, Interval):
            if isinstance(ref, LiquidApp):
                max_range = max_number if isinstance(
                    interval.sup, Infinity) else interval.sup  # or 2 ** 31 - 1
                max_range = max_range - 1 if interval.right_open else max_range

                min_range = min_number if isinstance(
                    interval.inf,
                    NegativeInfinity) else interval.inf  # or -2 ** 31
                min_range = min_range + 1 if interval.left_open else min_range

                metahandler_instance = gengy_metahandler(min_range, max_range)
                metahandler_type = Annotated[
                    python_type, metahandler_instance]  # type: ignore
                metahandler_list.append(metahandler_type)
            else:
                assert False
        elif isinstance(interval, EmptySet):
            pass
        else:
            assert False
    return metahandler_list


def get_metahandler_union(
    metahandler_list: list[MetaHandlerGenerator],
) -> MetaHandlerGenerator | Union[MetaHandlerGenerator]:
    if len(metahandler_list) == 1:
        return metahandler_list[0]
    else:
        return Union[tuple(metahandler_list)]


def refined_type_to_metahandler(
        ty: RefinedType) -> MetaHandlerGenerator | Union[MetaHandlerGenerator]:
    base_type_str = str(ty.type.name)
    gengy_metahandler = aeon_to_gengy_metahandlers[base_type_str]
    name, ref = ty.name, ty.refinement

    sympy_exp = refined_to_sympy_expression(ref)
    sympy_exp = simplify(sympy_exp)
    sympy_exp = to_dnf(sympy_exp)
    bounded_intervals = sympy_exp_to_bounded_interval(sympy_exp)
    intervals_list = split_or_intervals(bounded_intervals, name)
    metahandler_list = intervals_to_metahandlers(gengy_metahandler,
                                                 intervals_list, base_type_str,
                                                 ref)

    return get_metahandler_union(metahandler_list)


def create_abstract_class(class_name: str) -> type:
    """Create and return a new abstract class with the given name."""
    class_name = "t_" + class_name if not class_name.startswith(
        "t_") else class_name
    return make_dataclass(class_name, [], bases=(ABC, ))


def create_literal_class(class_name: str,
                         value_type: type | MetaHandlerGenerator,
                         base_class: type) -> type:
    """Create and return a new literal class with the given name and value type, based on the provided abstract class."""
    new_class = make_dataclass(
        "literal_" + class_name,
        [("value", value_type)],
        bases=(base_class, ),
    )
    return mk_method_core_literal(new_class)


def handle_refined_type(class_name: str, ty: RefinedType,
                        grammar_nodes: list[type]) -> tuple[list[type], type]:
    """Handle the creation of classes for refined types and update grammar nodes accordingly."""
    class_name = "t_" + class_name if not class_name.startswith(
        "t_") else class_name
    new_abs_class = create_abstract_class(class_name)
    grammar_nodes.append(new_abs_class)

    metahandler_type = refined_type_to_metahandler(ty)
    new_class = create_literal_class(class_name[2:], metahandler_type,
                                     new_abs_class)
    grammar_nodes.append(new_class)

    base_type_name = process_type_name(ty.type)
    grammar_nodes, _ = find_class_by_name(base_type_name, grammar_nodes)

    return grammar_nodes, new_abs_class


def find_class_by_name(class_name: str,
                       grammar_nodes: list[type],
                       ty: Type | None = None) -> tuple[list[type], type]:
    """This function iterates over the provided list of grammar nodes and
    returns the node whose name matches the provided name. If no match is found
    it creates a new abstract class and a new data class, adds them to the
    list, and returns the abstract class and the updated list of grammar nodes.

    Args:
        class_name (str): The name of the class to find.
        grammar_nodes (list[type]): A list of grammar nodes to search through.
        ty (Type): Aeon type of the class we are trying to find or create

    Returns:
        tuple[list[type], type]: A tuple containing the updated list of grammar nodes and the found or
        newly created class.
    """
    for cls in grammar_nodes:
        if cls.__name__ in [class_name, "t_" + class_name]:
            return grammar_nodes, cls

    if class_name in aeon_to_python_types:
        new_abs_class = create_abstract_class(class_name)
        grammar_nodes.append(new_abs_class)

        new_class = create_literal_class(class_name,
                                         aeon_to_python_types[class_name],
                                         new_abs_class)
        grammar_nodes.append(new_class)

        return grammar_nodes, new_abs_class

    if ty is not None and isinstance(ty, RefinedType) and str(
            ty.type.name) in aeon_to_gengy_metahandlers:
        return handle_refined_type(class_name, ty, grammar_nodes)

    new_abs_class = create_abstract_class(class_name)
    grammar_nodes.append(new_abs_class)
    return grammar_nodes, new_abs_class


def is_valid_class_name(class_name: str) -> bool:
    return class_name not in prelude_ops and not class_name.startswith(
        ("_anf_", "target"))


def get_attribute_type_name(attribute_type: Type,
                            parent_name: str = None) -> str:
    parent_name = parent_name or ""
    while isinstance(attribute_type, AbstractionType):
        parent_name += f"t_{process_type_name(attribute_type.var_type)}_"
        attribute_type = attribute_type.type
    attribute_type_name = f"t_{process_type_name(attribute_type)}"
    return parent_name + attribute_type_name


def generate_class_components(
    class_type: Type,
    grammar_nodes: list[type],
) -> tuple[list[type], list[tuple[str, type]], Type, str]:
    """Generates the attributes, superclass, and abstraction_type class name
    from a Type object.

    Args:
        class_type (Type): The class type to generate attributes and superclass for.
        grammar_nodes (List[Type]): The list of grammar nodes to search for classes.

    Returns:
        Tuple[List[Type], Dict[str, Type], Type, str]: A tuple containing the grammar_nodes list updated,
        attributes dictionary, the superclass, and the abstraction_type class name.
    """
    fields = []
    parent_name = ""
    while isinstance(class_type, AbstractionType):
        attribute_name = class_type.var_name.value if isinstance(
            class_type.var_name, Token) else class_type.var_name
        attribute_type = class_type.var_type

        attribute_type_name = get_attribute_type_name(attribute_type)

        grammar_nodes, cls = find_class_by_name(attribute_type_name,
                                                grammar_nodes, attribute_type)
        fields.append((attribute_name, cls))

        parent_name += f"{attribute_type_name}_"
        class_type = class_type.type

    class_type_str = process_type_name(class_type)

    superclass_type_name = f"{parent_name}t_{class_type_str}"

    return grammar_nodes, fields, class_type, superclass_type_name


def process_class_name(class_name: str) -> str:
    """Processes the class name depending on its type."""
    return class_name.value if isinstance(class_name, Token) else class_name


def create_new_class(class_name: str, parent_class: type, fields=None) -> type:
    """Creates a new class with the given name, parent class, and fields."""
    if fields is None:
        fields = []
    new_class = make_dataclass(class_name, fields, bases=(parent_class, ))
    new_class = mk_method_core(new_class)

    return new_class


def create_refined_class(
    class_name: str,
    parent_class: type,
    fields: list[tuple[str, type]],
    class_type: RefinedType,
    grammar_nodes: list[type],
) -> list[type]:
    """Create a refined class and update the grammar nodes list."""
    new_class_app = create_new_class(f"refined_app_{class_name}", parent_class,
                                     fields)
    grammar_nodes.append(new_class_app)

    parent_base_type_name = process_type_name(class_type.type)
    grammar_nodes, _ = find_class_by_name(parent_base_type_name, grammar_nodes,
                                          class_type.type)
    return grammar_nodes


def create_abstraction_class(class_name: str, abstraction_type_class_name: str,
                             grammar_nodes: list[type]) -> list[type]:
    """Create an abstraction class and update the grammar nodes list."""
    grammar_nodes, parent_class = find_class_by_name(
        abstraction_type_class_name, grammar_nodes)
    new_class_var = create_new_class(f"var_{class_name}", parent_class)
    grammar_nodes.append(new_class_var)
    return grammar_nodes


def create_class_from_ctx_var(var: tuple,
                              grammar_nodes: list[type]) -> list[type]:
    """Creates a new class based on a context variable and adds it to the list
    of grammar nodes.

    This function takes a context variable (a tuple with the class name and type) and a list of existing grammar nodes.
    It creates a new class or classes with the given name, and generate his attributes and superclass based on the type
    provided by the tuple.
    The new class or classes are then added to the list of grammar nodes.

    Args:
        var (tuple): A tuple containing the class name and type.
        grammar_nodes (list[type]): The list of existing grammar nodes.

    Returns:
        list[type]: The updated list of grammar nodes with the new class added,
        or the original list if no class was added.
    """
    class_name, class_type = var
    class_name = process_class_name(class_name)

    if not is_valid_class_name(class_name):
        return grammar_nodes

    class_name = aeon_prelude_ops_to_text.get(class_name, class_name)
    grammar_nodes, fields, parent_type, abstraction_type_class_name = generate_class_components(
        class_type, grammar_nodes)

    parent_class_name = process_type_name(parent_type)
    grammar_nodes, parent_class = find_class_by_name(parent_class_name,
                                                     grammar_nodes,
                                                     parent_type)

    if isinstance(class_type, RefinedType):
        grammar_nodes = create_refined_class(class_name, parent_class, fields,
                                             class_type, grammar_nodes)

    new_class_app = create_new_class(f"app_{class_name}", parent_class, fields)
    grammar_nodes.append(new_class_app)

    if isinstance(class_type, AbstractionType):
        grammar_nodes = create_abstraction_class(class_name,
                                                 abstraction_type_class_name,
                                                 grammar_nodes)

    return grammar_nodes


def create_if_class(class_name: str, parent_class_name: str,
                    grammar_nodes: list[type]) -> list[type]:
    grammar_nodes, cond_class = find_class_by_name("Bool", grammar_nodes)
    grammar_nodes, parent_class = find_class_by_name(parent_class_name,
                                                     grammar_nodes)

    fields = [("cond", cond_class), ("then", parent_class),
              ("otherwise", parent_class)]

    if_class = create_new_class(class_name, parent_class, fields)
    grammar_nodes.append(if_class)

    return grammar_nodes


def build_control_flow_grammar_nodes(grammar_nodes: list[type]) -> list[type]:
    types_names_set = {
        cls.__name__
        for cls in grammar_nodes if cls.__base__ is ABC and not any(
            issubclass(cls, other) and cls is not other
            for other in grammar_nodes)
    }
    for ty_name in types_names_set:
        grammar_nodes = create_if_class(f"If_{ty_name}", ty_name,
                                        grammar_nodes)
    return grammar_nodes


def gen_grammar_nodes(ctx: TypingContext,
                      synth_func_name: str,
                      metadata: Metadata,
                      grammar_nodes: list[type] | None = None) -> list[type]:
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
        else:
            return False

    for var_name, ty in ctx.vars():
        if not skip(var_name):
            grammar_nodes = create_class_from_ctx_var((var_name, ty),
                                                      grammar_nodes)

    return grammar_nodes


def convert_to_term(inp):
    if isinstance(inp, str):
        return Literal(inp, type=t_string)
    elif isinstance(inp, int):
        return Literal(inp, type=t_int)
    elif isinstance(inp, bool):
        return Literal(inp, type=t_bool)
    elif isinstance(inp, float):
        return Literal(inp, type=t_float)
    raise GrammarError(f"Unable to converto to term : {type(inp)}")


def print_grammar_nodes_names(grammar_nodes: list[type]) -> None:
    class_names = [cls.__name__ for cls in grammar_nodes]
    print(class_names)


def print_grammar_nodes(grammar_nodes: list[type]) -> None:
    for cls in grammar_nodes:
        parents = [base.__name__ for base in cls.__bases__]
        print("@dataclass")
        print(f"class {cls.__name__} ({''.join(parents)}):")
        class_vars = cls.__annotations__
        if class_vars:
            for var_name, var_type in class_vars.items():
                print(f"\t {var_name}: {var_type.__name__}")
        else:
            print("\t pass")
        print()
        # print("---------------------------------------------------")
