from __future__ import annotations

from abc import ABC
from dataclasses import make_dataclass
from typing import Generator, Optional, Tuple, Protocol
from typing import Type as TypingType

from geneticengine.grammar import extract_grammar, Grammar
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
from aeon.core.types import TypeConstructor
from aeon.core.types import RefinedType
from aeon.core.types import Top
from aeon.core.types import t_bool
from aeon.core.types import t_float
from aeon.core.types import t_int
from aeon.core.types import t_string
from aeon.decorators import Metadata
from aeon.synthesis.grammar.mangling import mangle_name, mangle_var, mangle_type
from aeon.synthesis.grammar.refinements import refined_type_to_metahandler
from aeon.synthesis.grammar.utils import prelude_ops, aeon_to_python
from aeon.typechecking.context import (
    TypeBinder,
    TypeConstructorBinder,
    TypingContext,
    TypingContextEntry,
    UninterpretedBinder,
    VariableBinder,
)
from aeon.core.liquid_ops import ops
from aeon.utils.name import Name, fresh_counter


VAR_WEIGHT = 10000
LITERAL_WEIGHT = 3000
IF_WEIGHT = 1
APP_WEIGHT = 1000
ABS_WEIGHT = 100


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
            return class_name[len(prefix) :]
    return class_name


class GrammarError(Exception):
    pass


# Protocol for classes that can have a get_core method
class HasGetCore(Protocol):
    def get_core(self): ...


classType = TypingType[HasGetCore]


def is_valid_class_name(class_name: str) -> bool:
    return class_name not in prelude_ops and not class_name.startswith(
        ("_anf_", "target"),
    )


ae_top = type("ae_top", (ABC,), {})


def extract_all_types(types: list[Type]) -> dict[Type, TypingType]:
    data: dict[Type, TypingType] = {Top(): ae_top}
    for ty in set(types):
        if ty not in data:
            match ty:
                case TypeConstructor(_, args):
                    assert not args, "Polytypes in not supported in Synthesis"
                    class_name = mangle_type(ty)
                    ty_abstract_class = type(
                        class_name,
                        (ae_top, ABC),
                        {},
                    )
                    # ty_abstract_class = abstract(ty_abstract_class)
                    ty_abstract_class = abstract(ty_abstract_class)
                    data[ty] = ty_abstract_class
                case RefinedType(_, itype, _):
                    class_name = mangle_type(ty)
                    data.update(extract_all_types([itype]))
                    parent = data[itype]
                    ty_abstract_class = type(class_name, (parent, ABC), {})
                    ty_abstract_class = abstract(ty_abstract_class)
                    data[ty] = ty_abstract_class
                    # TODO: alpha-equivalence
                    # TODO: subtyping
                case AbstractionType(var_name, var_type, return_type):
                    class_name = mangle_type(ty)
                    data.update(
                        extract_all_types(
                            [var_type, substitution_in_type(return_type, Var(Name("__self__", 0)), var_name)]
                        )
                    )
                    ty_abstract_class = type(class_name, (ae_top, ABC), {})
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

    def get_core(self):
        value = getattr(self, "value", None)
        return Literal(value, type=aeon_type)

    setattr(new_class, "get_core", get_core)
    new_class = weight(LITERAL_WEIGHT)(new_class)
    return new_class


def create_literals_nodes(type_info: dict[Type, TypingType], types: Optional[list[Type]] = None) -> list[TypingType]:
    """Creates all literal nodes for known types with literals (bool, int, float, string)"""
    if types is None:
        types = [t_bool, t_int, t_float, t_string]

    xname = Name("x", fresh_counter.fresh())

    gtm1 = LiquidApp(Name("<=", 0), [LiquidLiteralInt(-1), LiquidVar(xname)])
    lt256 = LiquidApp(Name("<=", 0), [LiquidVar(xname), LiquidLiteralInt(256)])
    base_int = [
        create_literal_class(
            t_int,
            type_info[t_int],
            refined_type_to_metahandler(RefinedType(xname, t_int, LiquidApp(Name("&&", 0), [gtm1, lt256]))),
        )
    ]

    return [create_literal_class(aeon_ty, type_info[aeon_ty]) for aeon_ty in types] + base_int


def create_literal_ref_nodes(type_info: dict[Type, TypingType] = None) -> list[TypingType]:
    """Creates all literal nodes for refined types, via metahandlers"""
    ref_types = [ty for ty in type_info if isinstance(ty, RefinedType) and ty.type in aeon_to_python]
    return [
        create_literal_class(aeon_ty, type_info[aeon_ty], refined_type_to_metahandler(aeon_ty)) for aeon_ty in ref_types
    ]


def create_var_node(name: Name, ty: Type, python_ty: TypingType) -> TypingType:
    """Creates a python type for a given variable in context."""
    vname = mangle_var(name)
    dc = make_dataclass(f"var_{vname}", [], bases=(python_ty,))

    def get_core(_):
        return Var(name)

    setattr(dc, "get_core", get_core)
    dc = weight(VAR_WEIGHT)(dc)
    return dc


def create_var_apps_node(name: Name, ty: AbstractionType, type_info: dict[Type, TypingType]) -> TypingType:
    """Creates a python type for a given variable in context that is a function."""

    # Collect arguments
    args: list[tuple[Name, Type]] = []
    current: Type = ty
    while isinstance(current, AbstractionType):
        args.append((current.var_name, current.var_type))
        current = current.type
    rtype = current
    python_ty = type_info[rtype]

    vname = mangle_var(name)
    dc = make_dataclass(
        f"var_app_{vname}", [(mangle_name(aname), type_info[ty]) for (aname, ty) in args], bases=(python_ty,)
    )

    def get_core(_self):
        current = Var(name)
        for aname, _ in args:
            current = Application(current, getattr(_self, mangle_name(aname)).get_core())

        return current

    setattr(dc, "get_core", get_core)
    dc = weight(VAR_WEIGHT)(dc)
    return dc


def create_var_nodes(vars: list[Tuple[Name, Type]], type_info: dict[Type, TypingType]) -> list[TypingType]:
    """Creates a list of python types for all variables in context."""
    return [create_var_node(var_name, ty, type_info[ty]) for (var_name, ty) in vars if ty in type_info] + [
        create_var_apps_node(var_name, ty, type_info)
        for (var_name, ty) in vars
        if ty in type_info and isinstance(ty, AbstractionType)
    ]


def create_abstraction_node(ty: AbstractionType, type_info: dict[Type, TypingType]) -> TypingType:
    """Creates a dataclass to represent an abstraction (\\_0 -> x) of type sth_arrow_X."""
    vname = f"lambda_{mangle_type(ty)}"
    dc = make_dataclass(vname, [("body", type_info[ty.type])], bases=(type_info[ty],))

    def get_core(_self):
        return Annotation(Abstraction(Name("_0", fresh_counter.fresh()), _self.body.get_core()), ty)

    # Note: We cannot use the variable inside Abstraction.
    setattr(dc, "get_core", get_core)
    dc = weight(ABS_WEIGHT)(dc)
    return dc


def collect_all_abstractions(t: Type) -> Generator[AbstractionType]:
    match t:
        case RefinedType(_, _, _) | TypeConstructor(_) | TypeVar() | Top():
            return
        case AbstractionType(_, aty, rty):
            yield t
            yield from collect_all_abstractions(aty)
            yield from collect_all_abstractions(rty)
        case TypePolymorphism(_, _, body):
            yield from collect_all_abstractions(body)
        case _:
            assert False, f"Unsupported {t}"


def create_abstraction_nodes(type_info: dict[Type, TypingType]) -> list[TypingType]:
    return [
        create_abstraction_node(ity, type_info)
        for ty in type_info
        for ity in collect_all_abstractions(ty)
        if isinstance(ity, AbstractionType)
    ]


def create_application_node(ty: AbstractionType, type_info: dict[Type, TypingType]) -> TypingType:
    """Creates a dataclass to represent an abstraction (\\_0 -> x) of type sth_arrow_X."""
    vname = f"app_{mangle_type(ty)}"
    dc = make_dataclass(vname, [("fun", type_info[ty]), ("arg", type_info[ty.var_type])], bases=(type_info[ty.type],))

    # Note: this would require dependent type dynamic processing on the return type (parent class)

    def get_core(_self):
        return Application(_self.fun.get_core(), _self.arg.get_core())

    setattr(dc, "get_core", get_core)
    dc = weight(APP_WEIGHT)(dc)
    return dc


def create_application_nodes(type_info: dict[Type, TypingType]) -> list[TypingType]:
    return [create_application_node(ty, type_info) for ty in type_info if isinstance(ty, AbstractionType)]


def create_if_node(ty: Type, type_info: dict[Type, TypingType]) -> TypingType:
    v_name = f"if_{mangle_type(ty)}"
    dc = make_dataclass(
        v_name,
        [("cond", type_info[t_bool]), ("then", type_info[ty]), ("otherwise", type_info[ty])],
        bases=(type_info[ty],),
    )

    def get_core(_self):
        return Annotation(If(_self.cond.get_core(), _self.then.get_core(), _self.otherwise.get_core()), ty)

    setattr(dc, "get_core", get_core)
    dc = weight(IF_WEIGHT)(dc)
    return dc


def create_if_nodes(type_info: dict[Type, TypingType]) -> list[TypingType]:
    return [create_if_node(ty, type_info) for ty in type_info]


def filter_uninterpreted(lt: LiquidTerm) -> Optional[LiquidTerm]:
    match lt:
        case LiquidHole():
            return lt
        case LiquidLiteralBool(_) | LiquidLiteralInt(_) | LiquidLiteralFloat(_) | LiquidLiteralString(_) | LiquidVar(_):
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
            assert False, f"Failed {lt}"


def remove_uninterpreted_functions_from_type(ty: Type) -> Type:
    match ty:
        case TypeConstructor(_, _) | TypeVar(_) | Top():
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
            return TypePolymorphism(name, kind, remove_uninterpreted_functions_from_type(body))
        case _:
            assert False, f"Unsupported {ty}"


def remove_uninterpreted_functions_wrap(e: TypingContextEntry) -> TypingContextEntry:
    match e:
        case VariableBinder(name, type):
            type = remove_uninterpreted_functions_from_type(type)
            return VariableBinder(name, type)
        case UninterpretedBinder(_, _) | TypeBinder(_, _) | TypeConstructorBinder(_, _):
            return e
        case _:
            assert False, f"Unsupported {e}"


def remove_uninterpreted_functions(ctx: TypingContext) -> TypingContext:
    return TypingContext([remove_uninterpreted_functions_wrap(el) for el in ctx.entries])


def propagate_constants(ctx: TypingContext) -> tuple[TypingContext, dict[Name, LiquidTerm]]:
    substitutions: dict[Name, LiquidTerm] = {}
    entries: list[TypingContextEntry] = []
    for e in ctx.entries:
        match e:
            case VariableBinder(name, ty):
                # Apply all pending substitions

                for k in substitutions:
                    ty = substitution_liquid_in_type(ty, substitutions[k], k)

                # Detect the pattern {n:T | n == C}
                match ty:
                    case RefinedType(name, _, LiquidApp(Name("==", _), [LiquidVar(iname), val])):
                        if name == iname:
                            substitutions[name] = val
                entries.append(VariableBinder(name, ty))
            case _:
                # TODO: we might want to apply the substitions on other types of entries
                entries.append(e)

    return TypingContext(entries), substitutions


def gen_grammar_nodes(
    ctx: TypingContext,
    ty: Type,
    synth_func_name: Name,
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
    ty = remove_uninterpreted_functions_from_type(ty)

    current_metadata = metadata.get(synth_func_name, {})
    is_recursion_allowed = current_metadata.get("recursion", False)
    vars_to_ignore = current_metadata.get("hide", [])
    types_to_ignore = current_metadata.get("hide_types", [])

    def skip(name: Name) -> bool:
        if name == synth_func_name:
            return not is_recursion_allowed
        elif name in vars_to_ignore:
            return True
        elif name.name.startswith("__internal__"):
            return True
        elif name.name in ["native", "native_import", "print"]:
            return True
        else:
            return False

    ctx_vars = [(var_name, ty) for (var_name, ty) in ctx.concrete_vars() if not skip(var_name)]
    types_to_consider = set([t_bool, t_float, t_int, t_string]) | set([x[1] for x in ctx_vars]) | set([ty])
    types_to_consider = types_to_consider - set(TypeConstructor(t) for t in types_to_ignore)
    type_info = extract_all_types(list(types_to_consider))
    type_nodes = list(set(type_info.values()))

    literals = create_literals_nodes(type_info)
    vars = create_var_nodes(ctx_vars, type_info)
    abstractions = create_abstraction_nodes(type_info)
    applications = create_application_nodes(type_info)
    literals_ref = create_literal_ref_nodes(type_info)
    ifs = create_if_nodes(type_info)

    ret = type_nodes + literals + literals_ref + vars + applications + abstractions
    if mangle_name(synth_func_name) in metadata and "disable_control_flow" in metadata[synth_func_name]:
        ret = ret + ifs
    return ret, type_info[ty]


def print_grammar_nodes_names(grammar_nodes: list[type]) -> None:
    class_names = [cls.__name__ for cls in grammar_nodes]
    print(class_names)


def print_grammar_nodes(grammar_nodes: list[type]) -> None:
    for cls in grammar_nodes:
        parents = [base.__name__ for base in cls.__bases__]
        print("@dataclass")
        print(f"class {cls.__name__}({', '.join(parents)}):")
        class_vars = cls.__annotations__
        if class_vars:
            for var_name, var_type in class_vars.items():
                print(f"\t {var_name}: {str(var_type)}")
        else:
            print("\t pass")
        print()
        # print("---------------------------------------------------")


def create_grammar(ctx: TypingContext, ty: Type, fun_name: Name, metadata: Metadata) -> Grammar:
    grammar_nodes, starting_node = gen_grammar_nodes(ctx, ty, fun_name, metadata, [])
    g = extract_grammar(grammar_nodes, starting_node)
    g = g.usable_grammar()
    return g
