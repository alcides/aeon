from __future__ import annotations

import traceback
from abc import ABC
from dataclasses import dataclass
from dataclasses import make_dataclass
from typing import Any
from typing import Callable
from typing import Optional

import numpy as np
import psb2
from geneticengine.algorithms.gp.individual import Individual
from geneticengine.algorithms.gp.simplegp import SimpleGP
from geneticengine.core.decorators import abstract
from geneticengine.core.grammar import extract_grammar
from geneticengine.core.grammar import Grammar
from geneticengine.core.problems import SingleObjectiveProblem
from geneticengine.metrics import mse
from lark.lexer import Token
from textdistance import levenshtein

from aeon.backend.evaluator import eval
from aeon.backend.evaluator import EvaluationContext
from aeon.core.substitutions import substitution
from aeon.core.substitutions import substitution_in_type
from aeon.core.terms import Abstraction
from aeon.core.terms import Annotation
from aeon.core.terms import Application
from aeon.core.terms import Hole
from aeon.core.terms import If
from aeon.core.terms import Let
from aeon.core.terms import Literal
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.core.types import AbstractionType
from aeon.core.types import Bottom
from aeon.core.types import RefinedType
from aeon.core.types import t_bool
from aeon.core.types import t_float
from aeon.core.types import t_int
from aeon.core.types import t_string
from aeon.core.types import Top
from aeon.core.types import top
from aeon.core.types import Type
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type_errors
from aeon.typechecking.typeinfer import synth

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
aeon_to_python_types = {"Int": int, "Bool": bool, "String": str, "Float": float}


# Probably move this method to another file
def refined_to_unrefined_type(ty: Type) -> Type:
    if isinstance(ty, RefinedType):
        return ty.type
    return ty


# dict (hole_name , (hole_type, hole_typingContext, func_name))
def get_holes_info(
    ctx: TypingContext,
    t: Term,
    ty: Type,
    holes: dict[str, tuple[Type, TypingContext, str]] = None,
    func_name: str = "",
) -> dict[str, tuple[Type, TypingContext, str]]:
    """Retrieve the Types of "holes" in a given Term and TypingContext.

    This function recursively navigates through the Term 't', updating the TypingContext and hole Type as necessary.
    When a hole is found, its Type and the current TypingContext are added to a dictionary, with the hole name as key.

    Args:
        ctx (TypingContext): The current TypingContext.
        t (Term): The term to analyze.
        ty (Type): The current type.
        holes (dict[str, tuple[Optional[Type], TypingContext]]): The current dictionary of hole types. Defaults to None.
        func_name (str) : The name of the function where the hole is defined.
    Returns:
        dict[str, tuple[Optional[Type], TypingContext]]: The updated dictionary of hole Types and their TypingContexts.
    """
    if holes is None:
        holes = {}
    if isinstance(t, Rec):
        if t.var_name.startswith("synth"):
            func_name = t.var_name
        ctx = ctx.with_var(t.var_name, t.var_type)
        holes = get_holes_info(ctx, t.var_value, t.var_type, holes, func_name)
        holes = get_holes_info(ctx, t.body, ty, holes, func_name)

    elif isinstance(t, Let):
        if t.var_name.startswith("synth"):
            func_name = t.var_name
        _, t1 = synth(ctx, t.var_value)
        ctx = ctx.with_var(t.var_name, t1)
        holes = get_holes_info(ctx, t.var_value, ty, holes, func_name)
        holes = get_holes_info(ctx, t.body, ty, holes, func_name)

    elif isinstance(t, Abstraction) and isinstance(ty, AbstractionType):
        ret = substitution_in_type(ty.type, Var(t.var_name), ty.var_name)
        ctx = ctx.with_var(t.var_name, ty.var_type)
        holes = get_holes_info(ctx, t.body, ret, holes, func_name)

    elif isinstance(t, If):
        holes = get_holes_info(ctx, t.then, ty, holes, func_name)
        holes = get_holes_info(ctx, t.otherwise, ty, holes, func_name)

    elif isinstance(t, Application):
        holes = get_holes_info(ctx, t.fun, ty, holes, func_name)
        holes = get_holes_info(ctx, t.arg, ty, holes, func_name)

    elif isinstance(t, Annotation) and isinstance(t.expr, Hole):
        synth_func_name = func_name
        ty = refined_to_unrefined_type(t.type)
        holes[t.expr.name] = (ty, ctx, synth_func_name)

    elif isinstance(t, Hole):
        ty = refined_to_unrefined_type(ty)
        holes[t.name] = (ty, ctx, func_name)

    return holes


def mk_method_core(cls: type):
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

    cls.get_core = get_core
    return cls


def mk_method_core_literal(cls: type):
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

    cls.get_core = get_core
    return cls


def find_class_by_name(class_name: str, grammar_nodes: list[type]) -> tuple[list[type], type]:
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
        new_abs_class = make_dataclass("t_" + class_name, [], bases=(ABC,))
        # new_abs_class = type("t_"+class_name, (), {})
        # new_abs_class = abstract(new_abs_class)
        grammar_nodes.append(new_abs_class)
        new_class = make_dataclass(
            "literal_" + class_name,
            [("value", aeon_to_python_types[class_name])],
            bases=(new_abs_class,),
        )

        new_class = mk_method_core_literal(new_class)

        grammar_nodes.append(new_class)

    else:
        class_name = class_name if class_name.startswith(
            "t_") else ("t_" + class_name)
        new_abs_class = make_dataclass(class_name, [], bases=(ABC,))
        grammar_nodes.append(new_abs_class)
    return grammar_nodes, new_abs_class


def is_valid_class_name(class_name: str) -> bool:
    return class_name not in prelude_ops and not class_name.startswith(("_anf_", "target"))


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
        # generate attributes
        attribute_name: str = (
            class_type.var_name.value if isinstance(
                class_type.var_name, Token) else class_type.var_name
        )

        attribute_type = (
            refined_to_unrefined_type(class_type.var_type)
            if isinstance(class_type.var_type, RefinedType)
            else class_type.var_type
        )

        grammar_nodes, cls = find_class_by_name(
            attribute_type.name, grammar_nodes)
        fields.append((attribute_name, cls))

        # generate abc class name for abstraction type e.g class t_Int_t_Int (ABC)
        parent_name += "t_" + attribute_type.name + "_"
        class_type = refined_to_unrefined_type(class_type.type)

    class_type_str = str(class_type) if isinstance(
        class_type, (Top, Bottom)) else class_type.name
    superclass_type_name: str = parent_name + "t_" + class_type_str

    return grammar_nodes, fields, class_type, superclass_type_name


def process_class_name(class_name: str) -> str:
    """Processes the class name depending on its type."""
    return class_name.value if isinstance(class_name, Token) else class_name


def create_new_class(class_name: str, parent_class: type, fields=None) -> type:
    """Creates a new class with the given name, parent class, and fields."""
    if fields is None:
        fields = []
    new_class = make_dataclass(class_name, fields, bases=(parent_class,))
    new_class = mk_method_core(new_class)

    return new_class


def create_class_from_ctx_var(var: tuple, grammar_nodes: list[type]) -> list[type]:
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
    parent_class_name = str(parent_type) if isinstance(
        parent_type, (Top, Bottom)) else parent_type.name
    grammar_nodes, parent_class = find_class_by_name(
        parent_class_name, grammar_nodes)

    new_class_app = create_new_class(f"app_{class_name}", parent_class, fields)
    grammar_nodes.append(new_class_app)

    # class var_function_name
    if isinstance(class_type, AbstractionType):
        grammar_nodes, parent_class = find_class_by_name(
            abstraction_type_class_name, grammar_nodes)

        new_class_var = create_new_class(f"var_{class_name}", parent_class)
        grammar_nodes.append(new_class_var)

    return grammar_nodes


def create_if_class(class_name: str, parent_class_name: str, grammar_nodes: list[type]) -> list[type]:
    grammar_nodes, cond_class = find_class_by_name("Bool", grammar_nodes)
    grammar_nodes, parent_class = find_class_by_name(
        parent_class_name, grammar_nodes)

    fields = [("cond", cond_class), ("then", parent_class),
              ("otherwise", parent_class)]

    if_class = create_new_class(class_name, parent_class, fields)
    grammar_nodes.append(if_class)

    return grammar_nodes


def build_control_flow_grammar_nodes(grammar_nodes: list[type]) -> list[type]:
    grammar_nodes_names_set = {cls.__name__ for cls in grammar_nodes}
    for base_type in grammar_base_types:
        if base_type in grammar_nodes_names_set:
            grammar_nodes = create_if_class(
                f"If_{base_type}", base_type, grammar_nodes)
    return grammar_nodes


def gen_grammar_nodes(ctx: TypingContext, synth_func_name: str, grammar_nodes: list[type] = None) -> list[type]:
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
    return next(
        (n for n in nodes if n.__name__ == node_name),
    )


def geneticengine(grammar: Grammar, fitness: Callable[[Individual], float]) -> Individual:
    alg = SimpleGP(
        grammar,
        problem=SingleObjectiveProblem(
            minimize=True,
            fitness_function=fitness,
        ),
        max_depth=8,
        number_of_generations=30,
        population_size=30,
        n_elites=1,
        verbose=2,
        target_fitness=0,
    )
    best = alg.evolve()
    return best


def load_dataset(dataset: str):
    return psb2.fetch_examples("path/to/PSB2/datasets/", dataset, 200, 2000, format="lists")


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


class Synthesizer:
    def __init__(
        self,
        ctx: TypingContext,
        p: Term,
        ty: Type = top,
        ectx: EvaluationContext = EvaluationContext(),
        genetic_engine: Callable = geneticengine,
    ):
        self.ctx = ctx
        self.p = p
        self.ty = ty
        self.ectx = ectx
        self.genetic_engine = genetic_engine

        self.holes = get_holes_info(ctx, p, ty)

        if len(self.holes) > 1:
            # self.train_data, self.test_data = load_dataset("twitter")
            self.train_data, self.test_data = load_dataset("gcd")

            first_hole_name = next(iter(self.holes))
            hole_type, hole_ctx, synth_func_name = self.holes[first_hole_name]

            grammar_n = gen_grammar_nodes(hole_ctx, synth_func_name)

            for cls in grammar_n:
                print(cls, "\nattributes: ", cls.__annotations__,
                    "\nparent class: ", cls.__bases__, "\n")
            assert len(grammar_n) > 0

            starting_node = get_grammar_node("t_" + hole_type.name, grammar_n)
            assert starting_node is not None, "Starting Node is None"

            grammar = extract_grammar(grammar_n, starting_node)
            print("g: ", grammar)

            if self.genetic_engine is not None:
                self.genetic_engine(grammar, self.fitness)
        else:
            eval(p, ectx)

    def fitness(self, individual) -> float:
        individual_term = individual.get_core()

        first_hole_name = next(iter(self.holes))
        _, _, synth_func_name = self.holes[first_hole_name]

        nt = substitution(self.p, individual_term, first_hole_name)

        try:
            check_type_errors(self.ctx, nt, self.ty)
        except Exception as e:
            # print(f"Check for type errors failed: {e}")
            # traceback.print_exception(e)
            return 100000000

        try:
            predicted_values = []
            true_values = []
            for datapoint in self.train_data:
                inputs, expected_output = datapoint
                # Apply the individual (which is a function) to the inputs
                fitness_eval_term = Var(synth_func_name)
                for inp in inputs:
                    fitness_eval_term = Application(
                        fitness_eval_term, convert_to_term(inp))

                nt_e = substitution(nt, fitness_eval_term, "main")
                actual_output = eval(nt_e, self.ectx)

                predicted_values.append(actual_output)
                true_values.append(expected_output[0])
            # provisional solution
            if isinstance(true_values[0], str):
                joined_true_values = " ".join(
                    word.strip() for word in true_values)
                joined_predicted_values = " ".join(
                    word.strip() for word in predicted_values)
                result = levenshtein(joined_true_values,
                                     joined_predicted_values)
            else:
                # Calculate mean squared error
                result = mse(np.array(predicted_values), np.array(true_values))
        except Exception as e:
            # print(f"Evaluation failed: {e}")
            # traceback.print_exception(e)
            result = 100000000
        return abs(result)
