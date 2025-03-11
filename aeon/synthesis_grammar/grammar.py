from __future__ import annotations

from abc import ABC
from dataclasses import make_dataclass
import sys
from typing import Optional, Tuple, Protocol
from typing import Type as TypingType

from geneticengine.grammar.decorators import weight
from geneticengine.grammar.metahandlers.base import MetaHandlerGenerator
from geneticengine.prelude import abstract

from aeon.core.liquid import (
    LiquidApp,
    LiquidHole,
    LiquidLiteralBool,
    LiquidLiteralFloat,
    LiquidLiteralInt,
    LiquidLiteralString,
    LiquidTerm,
    LiquidVar,
)
from aeon.core.substitutions import substitution_in_type, substitution_liquid_in_type
from aeon.core.terms import Abstraction, Annotation, Application, If, Literal
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, Type, TypePolymorphism, TypeVar
from aeon.core.types import BaseType
from aeon.core.types import RefinedType
from aeon.core.types import Top
from aeon.core.types import t_bool
from aeon.core.types import t_float
from aeon.core.types import t_int
from aeon.core.types import t_string
from aeon.decorators import Metadata
from aeon.synthesis_grammar.mangling import mangle_var, mangle_type
from aeon.synthesis_grammar.refinements import refined_type_to_metahandler
from aeon.synthesis_grammar.utils import prelude_ops, aeon_to_python
from aeon.typechecking.context import (
    EmptyContext,
    TypeBinder,
    TypingContext,
    UninterpretedBinder,
    VariableBinder,
    concrete_vars_in,
)
from aeon.core.liquid_ops import ops

VAR_WEIGHT = 100
LITERAL_WEIGHT = 30
IF_WEIGHT = 1
APP_WEIGHT = 10
ABS_WEIGHT = 1

max_number = sys.maxsize - 1
min_number = -(sys.maxsize - 1)


def extract_class_name(class_name: str) -> str:
    prefixes = [
        "var_",
        "app_",
        "refined_app_",
        "refined_var_",
        "literal_Refined_",
        "literal_",
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


def is_valid_class_name(class_name: str) -> bool:
    return class_name not in prelude_ops and not class_name.startswith(
        ("_anf_", "target"), )


ae_top = type("ae_top", (ABC, ), {})


def extract_all_types(types: list[Type]) -> dict[Type, TypingType]:
    data: dict[Type, TypingType] = {Top(): ae_top}
    for ty in types:
        match ty:
            case BaseType(_):
                class_name = mangle_type(ty)
                ty_abstract_class = type(class_name, (ae_top, ), {})
                ty_abstract_class = abstract(ty_abstract_class)
                data[ty] = ty_abstract_class
            case RefinedType(_, itype, _):
                data.update(extract_all_types([itype]))
                parent = data[itype]
                ty_abstract_class = type(class_name, (parent, ), {})
                ty_abstract_class = abstract(ty_abstract_class)
                data[ty] = ty_abstract_class
                # TODO: alpha-equivalence
                # TODO: subtyping
            case AbstractionType(var_name, var_type, return_type):
                class_name = mangle_type(ty)
                data.update(
                    extract_all_types([
                        var_type,
                        substitution_in_type(return_type, Var("__self__"),
                                             var_name)
                    ]))
                ty_abstract_class = type(class_name, (ae_top, ), {})
                ty_abstract_class = abstract(ty_abstract_class)
                data[ty] = ty_abstract_class
                # TODO: alpha-equivalence
            case Top():
                data[ty] = ae_top
            case TypePolymorphism(_, _, _):
                # TODO: Polytypes in Synthesis
                continue
            case _:
                assert False, f"Unsupported {ty}"
    return data


def create_literal_class(
        aeon_type: Type,
        parent_class: type,
        value_type: None | type | MetaHandlerGenerator = None) -> type:
    """Create and return a new literal class with the given name and value type, based on the provided abstract class."""
    if value_type is None:
        value_type = aeon_to_python[aeon_type]

    class_name = mangle_type(aeon_type)
    new_class = make_dataclass(
        f"literal_{class_name}",
        [("value", value_type)],
        bases=(parent_class, ),
    )

    def get_core(self):
        value = getattr(self, "value", None)
        return Literal(value, type=aeon_type)

    setattr(new_class, "get_core", get_core)
    new_class = weight(LITERAL_WEIGHT)(new_class)
    return new_class


def create_literals_nodes(
        type_info: dict[Type, TypingType],
        types: Optional[list[Type]] = None) -> list[TypingType]:
    """Creates all literal nodes for known types with literals (bool, int, float, string)"""
    if types is None:
        types = [t_bool, t_int, t_float, t_string]

    gtm1 = LiquidApp("<=", [LiquidLiteralInt(-1), LiquidVar("x")])
    lt256 = LiquidApp("<=", [LiquidVar("x"), LiquidLiteralInt(256)])
    base_int = [
        create_literal_class(
            t_int,
            type_info[t_int],
            refined_type_to_metahandler(
                RefinedType("x", t_int, LiquidApp("&&", [gtm1, lt256]))),
        )
    ]

    return [
        create_literal_class(aeon_ty, type_info[aeon_ty]) for aeon_ty in types
    ] + base_int


def create_literal_ref_nodes(
        type_info: dict[Type, TypingType] = None) -> list[TypingType]:
    """Creates all literal nodes for refined types, via metahandlers"""
    ref_types = [
        ty for ty in type_info
        if isinstance(ty, RefinedType) and ty.type in aeon_to_python
    ]
    return [
        create_literal_class(aeon_ty, type_info[aeon_ty],
                             refined_type_to_metahandler(aeon_ty))
        for aeon_ty in ref_types
    ]


def create_var_node(name: str, ty: Type, python_ty: TypingType) -> TypingType:
    """Creates a python type for a given variable in context."""
    vname = mangle_var(name)
    dc = make_dataclass(f"var_{vname}", [], bases=(python_ty, ))

    def get_core(_):
        return Var(name)

    setattr(dc, "get_core", get_core)
    dc = weight(VAR_WEIGHT)(dc)
    return dc


def create_var_nodes(vars: list[Tuple[str, Type]],
                     type_info: dict[Type, TypingType]) -> list[TypingType]:
    """Creates a list of python types for all variables in context."""
    return [
        create_var_node(var_name, ty, type_info[ty]) for (var_name, ty) in vars
        if ty in type_info
    ]


def create_abstraction_node(ty: AbstractionType,
                            type_info: dict[Type, TypingType]) -> TypingType:
    """Creates a dataclass to represent an abstraction (\\_0 -> x) of type sth_arrow_X."""
    vname = f"lambda_{mangle_type(ty)}"
    dc = make_dataclass(vname, [("body", type_info[ty.type])],
                        bases=(type_info[ty], ))

    def get_core(_self):
        return Annotation(Abstraction("_0", _self.body.get_core()), ty)

    # Note: We cannot use the variable inside Abstraction.
    setattr(dc, "get_core", get_core)
    dc = weight(ABS_WEIGHT)(dc)
    return dc


def create_abstraction_nodes(
        type_info: dict[Type, TypingType]) -> list[TypingType]:
    return [
        create_abstraction_node(ty, type_info) for ty in type_info
        if isinstance(ty, AbstractionType)
    ]


def create_application_node(ty: AbstractionType,
                            type_info: dict[Type, TypingType]) -> TypingType:
    """Creates a dataclass to represent an abstraction (\\_0 -> x) of type sth_arrow_X."""
    vname = f"app_{mangle_type(ty)}"
    dc = make_dataclass(vname, [("fun", type_info[ty]),
                                ("arg", type_info[ty.var_type])],
                        bases=(type_info[ty.type], ))

    # Note: this would require dependent type dynamic processing on the return type (parent class)

    def get_core(_self):
        return Application(_self.fun.get_core(), _self.arg.get_core())

    setattr(dc, "get_core", get_core)
    dc = weight(APP_WEIGHT)(dc)
    return dc


def create_application_nodes(
        type_info: dict[Type, TypingType]) -> list[TypingType]:
    return [
        create_application_node(ty, type_info) for ty in type_info
        if isinstance(ty, AbstractionType)
    ]


def create_if_node(ty: Type, type_info: dict[Type, TypingType]) -> TypingType:
    v_name = f"if_{mangle_type(ty)}"
    dc = make_dataclass(
        v_name,
        [("cond", type_info[t_bool]), ("then", type_info[ty]),
         ("otherwise", type_info[ty])],
        bases=(type_info[ty], ),
    )

    def get_core(_self):
        return Annotation(
            If(_self.cond.get_core(), _self.then.get_core(),
               _self.otherwise.get_core()), ty)

    setattr(dc, "get_core", get_core)
    dc = weight(IF_WEIGHT)(dc)
    return dc


def create_if_nodes(type_info: dict[Type, TypingType]) -> list[TypingType]:
    return [create_if_node(ty, type_info) for ty in type_info]


def filter_uninterpreted(lt: LiquidTerm) -> Optional[LiquidTerm]:
    match lt:
        case LiquidHole():
            return lt
        case LiquidLiteralBool(_) | LiquidLiteralInt(_) | LiquidLiteralFloat(
            _) | LiquidLiteralString(_) | LiquidVar(_):
            return lt
        case LiquidApp(fun, args):
            if fun in ["&&", "||"]:
                nargs = [filter_uninterpreted(x) for x in args]
                if nargs[0] is None:
                    return nargs[1]
                if nargs[1] is None:
                    return nargs[0]
                return LiquidApp(fun, nargs)
            elif fun in ops:
                nargs = [filter_uninterpreted(x) for x in args]
                if None not in nargs:
                    return LiquidApp(fun, nargs)
                else:
                    return None
            else:
                # user-defined uninterpreted function
                return None
        case _:
            assert False


def remove_uninterpreted_functions_from_type(ty: Type) -> Type:
    match ty:
        case BaseType() | TypeVar() | Top():
            return ty
        case AbstractionType(var_name, var_type, type):
            return AbstractionType(
                var_name,
                remove_uninterpreted_functions_from_type(var_type),
                remove_uninterpreted_functions_from_type(type),
            )
        case RefinedType(name, type, ref):
            ref_filtered = filter_uninterpreted(ref)
            if ref_filtered is None:
                return type
            else:
                return RefinedType(name, type, ref_filtered)
        case TypePolymorphism(name, kind, body):
            return TypePolymorphism(
                name, kind, remove_uninterpreted_functions_from_type(body))
        case _:
            assert False, f"Unsupported {ty}"


def remove_uninterpreted_functions(ctx: TypingContext) -> TypingContext:
    match ctx:
        case EmptyContext():
            return ctx
        case UninterpretedBinder(prev, name, type):
            return UninterpretedBinder(remove_uninterpreted_functions(prev),
                                       name, type)
        case VariableBinder(prev, name, type):
            type = remove_uninterpreted_functions_from_type(type)
            return VariableBinder(remove_uninterpreted_functions(prev), name,
                                  type)
        case TypeBinder(prev, type_name, type_kind):
            return TypeBinder(remove_uninterpreted_functions(prev), type_name,
                              type_kind)
        case _:
            assert False


def propagate_constants(
        ctx: TypingContext) -> tuple[TypingContext, dict[str, LiquidTerm]]:
    match ctx:
        case EmptyContext():
            return ctx, {}
        case UninterpretedBinder(prev, name, type):
            p, subst = propagate_constants(prev)
            return UninterpretedBinder(p, name, type), subst
        case VariableBinder(prev, name, type):
            p, subst = propagate_constants(prev)

            # Apply all pending substitions

            for k in subst:
                type = substitution_liquid_in_type(type, subst[k], k)

            # Detect the pattern {n:T | n == C}
            if (isinstance(type, RefinedType)
                    and isinstance(type.refinement, LiquidApp)
                    and type.refinement.fun == "=="
                    and type.refinement.args[0] == LiquidVar(type.name)):
                v = type.refinement.args[1]
                subst[name] = v

            return VariableBinder(p, name, type), subst
        case TypeBinder(prev, type_name, type_kind):
            p, subst = propagate_constants(prev)
            return TypeBinder(p, type_name, type_kind), subst
        case _:
            assert False


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

    # Clean context to remove non-interpreted functions from the context.
    # Simple refinements like 0 < n && n < 10 are kept.
    ctx, _ = propagate_constants(ctx)
    ctx = remove_uninterpreted_functions(ctx)
    synth_fun_type = remove_uninterpreted_functions_from_type(synth_fun_type)

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

    ctx_vars = [(var_name, ty) for (var_name, ty) in concrete_vars_in(ctx)
                if not skip(var_name)]
    type_info = extract_all_types([t_bool, t_float, t_int, t_string] +
                                  [x[1] for x in ctx_vars] + [synth_fun_type])
    type_nodes = list(type_info.values())

    literals = create_literals_nodes(type_info)
    vars = create_var_nodes(ctx_vars, type_info)
    abstractions = create_abstraction_nodes(type_info)
    applications = create_application_nodes(type_info)
    literals_ref = create_literal_ref_nodes(type_info)
    ifs = create_if_nodes(type_info)

    ret = type_nodes + literals + literals_ref + vars + applications + ifs + abstractions
    return ret, type_info[synth_fun_type]


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
                print(f"\t {var_name}: {str(var_type)}")
        else:
            print("\t pass")
        print()
        # print("---------------------------------------------------")
