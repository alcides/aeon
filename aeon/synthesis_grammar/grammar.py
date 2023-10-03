from __future__ import annotations

from abc import ABC
from dataclasses import make_dataclass
from typing import Protocol
from typing import Type as TypingType

from lark.lexer import Token

from aeon.core.terms import Application
from aeon.core.terms import If
from aeon.core.terms import Literal
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, Type, TypeVar
from aeon.core.types import BaseType
from aeon.core.types import Bottom
from aeon.core.types import refined_to_unrefined_type
from aeon.core.types import RefinedType
from aeon.core.types import t_bool
from aeon.core.types import t_float
from aeon.core.types import t_int
from aeon.core.types import t_string
from aeon.core.types import Top
from aeon.typechecking.context import TypingContext

prelude_ops = ["print", "native_import", "native"]

aeon_prelude_ops_to_text = {
    "%": "mod",
    "/": "div",
    "*": "mult",
    "-": "sub",
    "+": "add",
    "%.": "mod_f",
    "/.": "div_f",
    "*.": "mult_f",
    "-.": "sub_f",
    "+.": "add_f",
    ">=": "greater_equal",
    ">": "greater_than",
    "<=": "less_equal",
    "<": "less_than",
    "!=": "not_equal",
    "==": "equal",
}
text_to_aeon_prelude_ops = {v: k for k, v in aeon_prelude_ops_to_text.items()}

grammar_base_types = ["t_Float", "t_Int", "t_String", "t_Bool"]
aeon_to_python_types = {
    "Int": int,
    "Bool": bool,
    "String": str,
    "Float": float
}


# Protocol for classes that can have a get_core method
class HasGetCore(Protocol):

    def get_core(self):
        ...


classType = TypingType[HasGetCore]


def mk_method_core(cls: classType) -> classType:

    def get_core(self):
        class_name = self.__class__.__name__
        # the prefix is either "var_" or "app_"
        class_name_without_prefix = class_name[4:]

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
            for attr_name, _ in cls.__annotations__.items():
                value = getattr(self, attr_name, None)
                if_dict[attr_name] = value.get_core

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
        class_name_without_prefix = class_name[8:]
        value = getattr(self, "value", None)
        try:
            if value is not None:
                if class_name_without_prefix == "Int":
                    base = Literal(int(value), type=t_int)
                elif class_name_without_prefix == "Float":
                    base = Literal(float(value), type=t_float)
                elif class_name_without_prefix == "Bool":
                    value = str(value) == "true"
                    base = Literal(value, type=t_bool)
                elif class_name_without_prefix == "String":
                    v = str(value)[1:-1]
                    base = Literal(str(v), type=t_string)

                return base
        except Exception as e:
            raise Exception("no value\n ", e)

    setattr(cls, "get_core", get_core)
    return cls


def find_class_by_name(class_name: str,
                       grammar_nodes: list[type]) -> tuple[list[type], type]:
    """This function iterates over the provided list of grammar nodes and
    returns the node whose name matches the provided name. If no match is found
    it creates a new abstract class and a new data class, adds them to the
    list, and returns the abstract class and the updated list of grammar nodes.

    Args:
        class_name (str): The name of the class to find.
        grammar_nodes (list[type]): A list of grammar nodes to search through.

    Returns:
        tuple[list[type], type]: A tuple containing the updated list of grammar nodes and the found or newly created class.
    """
    for cls in grammar_nodes:
        if cls.__name__ in [class_name, "t_" + class_name]:
            return grammar_nodes, cls
    if class_name in list(aeon_to_python_types.keys()):
        new_abs_class = make_dataclass("t_" + class_name, [], bases=(ABC, ))
        # new_abs_class = type("t_"+class_name, (), {})
        # new_abs_class = abstract(new_abs_class)
        grammar_nodes.append(new_abs_class)
        new_class = make_dataclass(
            "literal_" + class_name,
            [("value", aeon_to_python_types[class_name])],
            bases=(new_abs_class, ),
        )

        new_class = mk_method_core_literal(new_class)

        grammar_nodes.append(new_class)

    else:
        class_name = class_name if class_name.startswith("t_") else (
            "t_" + class_name)
        new_abs_class = make_dataclass(class_name, [], bases=(ABC, ))
        grammar_nodes.append(new_abs_class)
    return grammar_nodes, new_abs_class


def is_valid_class_name(class_name: str) -> bool:
    return class_name not in prelude_ops and not class_name.startswith(
        ("_anf_", "target"))


def get_attribute_type_name(attribute_type, parent_name=None):
    parent_name = parent_name or ""
    while isinstance(attribute_type, AbstractionType):
        attribute_type = refined_to_unrefined_type(attribute_type.type)
        parent_name += f"t_{get_attribute_type_name(attribute_type, parent_name)}_"
    return parent_name + attribute_type.name if isinstance(
        attribute_type, BaseType) else parent_name


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
        attribute_type = (refined_to_unrefined_type(class_type.var_type)
                          if isinstance(class_type.var_type, RefinedType) else
                          class_type.var_type)
        attribute_type_name = get_attribute_type_name(attribute_type)

        grammar_nodes, cls = find_class_by_name(attribute_type_name,
                                                grammar_nodes)
        fields.append((attribute_name, cls))

        parent_name += f"t_{attribute_type_name}_"
        class_type = refined_to_unrefined_type(class_type.type)

    if isinstance(class_type, Top) or isinstance(class_type, Bottom):
        class_type_str = str(class_type)
    elif isinstance(class_type, BaseType):
        class_type_str = class_type.name
    else:
        assert False

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
    class_type = refined_to_unrefined_type(class_type)

    class_name = process_class_name(class_name)

    if not is_valid_class_name(class_name):
        return grammar_nodes

    class_name = aeon_prelude_ops_to_text.get(class_name, class_name)

    grammar_nodes, fields, parent_type, abstraction_type_class_name = generate_class_components(
        class_type,
        grammar_nodes,
    )

    # class app_function_name
    if isinstance(parent_type, (Top, Bottom)):
        parent_class_name: str = str(parent_type)
    elif isinstance(parent_type, (BaseType, TypeVar)):
        parent_class_name = parent_type.name
    else:
        raise Exception(f"parent class name not definied: {(parent_type)}")
    grammar_nodes, parent_class = find_class_by_name(parent_class_name,
                                                     grammar_nodes)

    new_class_app = create_new_class(f"app_{class_name}", parent_class, fields)
    grammar_nodes.append(new_class_app)

    # class var_function_name
    if isinstance(class_type, AbstractionType):
        grammar_nodes, parent_class = find_class_by_name(
            abstraction_type_class_name, grammar_nodes)

        new_class_var = create_new_class(f"var_{class_name}", parent_class)
        grammar_nodes.append(new_class_var)

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
    grammar_nodes_names_set = {cls.__name__ for cls in grammar_nodes}
    for base_type in grammar_base_types:
        if base_type in grammar_nodes_names_set:
            grammar_nodes = create_if_class(f"If_{base_type}", base_type,
                                            grammar_nodes)
    return grammar_nodes


def gen_grammar_nodes(ctx: TypingContext,
                      synth_func_name: str,
                      grammar_nodes: list[type] | None = None) -> list[type]:
    """Generate grammar nodes from the variables in the given TypingContext.

    This function iterates over the variables in the provided TypingContext. For each variable,
    it generates a new class using the create_class_from_ctx_var function and adds it to
    the list of grammar_nodes. If no initial list of grammar_nodes is provided, it starts with an empty list.

    Args:
        ctx (TypingContext): The TypingContext to extract variables from.
        synth_func_name (str) : The name of the function where the hole is located
        grammar_nodes (list[type]): Initial list of grammar nodes. Defaults to an empty list.

    Returns:
        list[type]: The list of generated grammar nodes.
    """
    if grammar_nodes is None:
        grammar_nodes = []
    for var in ctx.vars():
        if var[0] != synth_func_name:
            grammar_nodes = create_class_from_ctx_var(var, grammar_nodes)
    grammar_nodes = build_control_flow_grammar_nodes(grammar_nodes)
    return grammar_nodes


def get_grammar_node(node_name: str, nodes: list[type]) -> type | None:
    """Returns the node from the provided list of nodes whose name matches the
    provided name. If no match is found, the function returns None.

    Args:
        node_name (str): The name of the node to retrieve.
        nodes (list[type]): A list of nodes to search through.

    Returns:
        type: The node with the matching name
    """
    return next((n for n in nodes if n.__name__ == node_name), )


def convert_to_term(inp):
    if isinstance(inp, str):
        return Literal(inp, type=t_string)
    elif isinstance(inp, int):
        return Literal(inp, type=t_int)
    elif isinstance(inp, bool):
        return Literal(inp, type=t_bool)
    elif isinstance(inp, float):
        return Literal(inp, type=t_float)
    raise Exception(f"unable to converto to term : {type(inp)}")
