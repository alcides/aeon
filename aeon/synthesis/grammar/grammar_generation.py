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
from itertools import product

from aeon.core.substitutions import substitute_vartype, substitution_in_type, substitution_liquid_in_type
from aeon.core.terms import Abstraction, Annotation, Application, If, Literal, TypeApplication
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, RefinementPolymorphism, Type, TypePolymorphism, TypeVar
from aeon.core.types import TypeConstructor
from aeon.core.types import RefinedType
from aeon.core.types import Top
from aeon.core.types import refined_to_unrefined_type
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
                    if args:
                        data.update(extract_all_types(list(args)))
                    class_name = mangle_type(ty)
                    ty_abstract_class = type(
                        class_name,
                        (ae_top, ABC),
                        {},
                    )
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
    """Creates all literal nodes for known types with literals (bool, int, float, string).

    For Int, the unlimited-range literal is replaced by a metahandler-based literal
    (IntRange(-1, 256)) to avoid the enumerative search iterating over hundreds of
    millions of values before finding valid ones.
    """
    if types is None:
        types = [t_bool, t_int, t_float, t_string]

    xname = Name("x", fresh_counter.fresh())

    gtm1 = LiquidApp(Name("<=", 0), [LiquidLiteralInt(-1), LiquidVar(xname)])
    lt256 = LiquidApp(Name("<=", 0), [LiquidVar(xname), LiquidLiteralInt(256)])
    base_int = create_literal_class(
        t_int,
        type_info[t_int],
        refined_type_to_metahandler(RefinedType(xname, t_int, LiquidApp(Name("&&", 0), [gtm1, lt256]))),
    )

    # Exclude t_int from the unlimited-range list; use the metahandler-based base_int instead.
    types_without_unlimited_int = [ty for ty in types if ty != t_int]
    return [create_literal_class(aeon_ty, type_info[aeon_ty]) for aeon_ty in types_without_unlimited_int] + [base_int]


def create_literal_ref_nodes(type_info: dict[Type, TypingType] = None) -> list[TypingType]:
    """Creates literal nodes for refined types using metahandlers.

    Each node:
    - Uses a metahandler (e.g. IntRange(1, 99)) so the enumerative search only
      iterates values that satisfy the refinement.
    - Inherits from the BASE type's grammar class (e.g. æInt) so it is a direct
      alternative for that class in the grammar — no refined abstract class needed.
    - Returns a Literal with the base (unrefined) type from get_core() so the
      type checker can handle it correctly.
    """
    ref_types = [ty for ty in type_info if isinstance(ty, RefinedType) and ty.type in aeon_to_python]
    result = []
    for aeon_ty in ref_types:
        base_type = aeon_ty.type
        # Parent is the BASE type's class (e.g. æInt), not the refined abstract class.
        parent_class = type_info[base_type]
        metahandler = refined_type_to_metahandler(aeon_ty)
        if metahandler is None:
            continue
        lit_class = create_literal_class(aeon_ty, parent_class, metahandler)

        def get_core(self, bt=base_type):
            value = getattr(self, "value", None)
            return Literal(value, type=bt)

        setattr(lit_class, "get_core", get_core)
        result.append(lit_class)
    return result


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
        case RefinementPolymorphism(_, _, body):
            return remove_uninterpreted_functions_from_type(body)
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
                    case RefinedType(rname, _, LiquidApp(Name("==", _), [LiquidVar(iname), val])):
                        if rname == iname:
                            substitutions[rname] = val
                entries.append(VariableBinder(name, ty))
            case _:
                # TODO: we might want to apply the substitions on other types of entries
                entries.append(e)

    return TypingContext(entries), substitutions


def _collect_tcs(ty: Type, result: set[TypeConstructor]):
    """Recursively collect all TypeConstructor instances from a type."""
    match ty:
        case TypeConstructor(_, args):
            result.add(ty)
            for arg in args:
                _collect_tcs(arg, result)
        case RefinedType(_, inner, _):
            _collect_tcs(inner, result)
        case AbstractionType(_, var_type, ret_type):
            _collect_tcs(var_type, result)
            _collect_tcs(ret_type, result)
        case TypePolymorphism(_, _, body):
            _collect_tcs(body, result)
        case RefinementPolymorphism(_, sort, body):
            _collect_tcs(sort, result)
            _collect_tcs(body, result)
        case _:
            pass


def _collect_type_arg_types(ty: Type, result: set[TypeConstructor]):
    """Collect types used as arguments to parameterized TypeConstructors."""
    match ty:
        case TypeConstructor(_, args):
            for arg in args:
                if isinstance(arg, TypeConstructor):
                    result.add(arg)
                _collect_type_arg_types(arg, result)
        case RefinedType(_, inner, _):
            _collect_type_arg_types(inner, result)
        case AbstractionType(_, var_type, ret_type):
            _collect_type_arg_types(var_type, result)
            _collect_type_arg_types(ret_type, result)
        case TypePolymorphism(_, _, body):
            _collect_type_arg_types(body, result)
        case _:
            pass


def monomorphize_poly_type(
    ty: TypePolymorphism,
    instantiation_types: set[TypeConstructor],
) -> list[tuple[Type, list[Type]]]:
    """Monomorphize a polymorphic type by instantiating forall-bound vars with candidate types.

    Args:
        ty: The polymorphic type to monomorphize.
        instantiation_types: Types to use for instantiation (should be non-parametric types
            that actually appear as type arguments in the program).

    Returns list of (monomorphized_body, type_applications) pairs.
    """
    foralls: list[Name] = []
    current: Type = ty
    while isinstance(current, TypePolymorphism):
        foralls.append(current.name)
        current = current.body

    # Skip types with RefinementPolymorphism (e.g. $)
    if isinstance(current, RefinementPolymorphism):
        return []

    base_types = list(instantiation_types)
    if not base_types:
        return []

    results = []
    for combo in product(base_types, repeat=len(foralls)):
        body = current
        type_apps: list[Type] = list(combo)
        for tvar_name, concrete_ty in zip(foralls, combo):
            body = substitute_vartype(body, concrete_ty, tvar_name)
        results.append((body, type_apps))

    return results


def create_monomorphized_var_nodes(
    monomorphized: list[tuple[Name, Type, list[Type]]],
    type_info: dict[Type, TypingType],
) -> list[TypingType]:
    """Create grammar nodes for monomorphized polymorphic variables."""
    nodes: list[TypingType] = []
    for name, mono_ty, type_apps in monomorphized:
        # Simple var node (produces the type-applied function/value)
        if mono_ty in type_info:
            vname = mangle_var(name) + "_mono_" + "_".join(mangle_type(t) for t in type_apps)
            dc = make_dataclass(f"var_{vname}", [], bases=(type_info[mono_ty],))

            def get_core(_, _name=name, _ta=type_apps):
                term = Var(_name)
                for t in _ta:
                    term = TypeApplication(term, t)
                return term

            setattr(dc, "get_core", get_core)
            dc = weight(VAR_WEIGHT)(dc)
            nodes.append(dc)

        # Fully-applied function node
        if isinstance(mono_ty, AbstractionType):
            args: list[tuple[Name, Type]] = []
            current: Type = mono_ty
            while isinstance(current, AbstractionType):
                args.append((current.var_name, current.var_type))
                current = current.type
            rtype = current

            if rtype not in type_info or any(aty not in type_info for _, aty in args):
                continue

            vname = mangle_var(name) + "_mono_" + "_".join(mangle_type(t) for t in type_apps)
            dc = make_dataclass(
                f"var_app_{vname}",
                [(mangle_name(aname), type_info[aty]) for (aname, aty) in args],
                bases=(type_info[rtype],),
            )

            args_names = [aname for aname, _ in args]

            def get_core_app(_self, _name=name, _ta=type_apps, _args=args_names):
                term = Var(_name)
                for t in _ta:
                    term = TypeApplication(term, t)
                for aname in _args:
                    term = Application(term, getattr(_self, mangle_name(aname)).get_core())
                return term

            setattr(dc, "get_core", get_core_app)
            dc = weight(APP_WEIGHT)(dc)
            nodes.append(dc)

    return nodes


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
    vars_to_ignore_names = {v.name for v in vars_to_ignore}
    types_to_ignore = current_metadata.get("hide_types", [])

    def skip(name: Name) -> bool:
        if name == synth_func_name:
            return not is_recursion_allowed
        elif name.name in vars_to_ignore_names:
            return True
        elif name.name.startswith("__internal__"):
            return True
        elif name.name in ["native", "native_import", "print"]:
            return True
        else:
            return False

    ctx_vars = [(var_name, ty) for (var_name, ty) in ctx.concrete_vars() if not skip(var_name)]

    # Separate polymorphic and monomorphic context variables
    poly_ctx_vars = [(vn, vt) for (vn, vt) in ctx_vars if isinstance(vt, TypePolymorphism)]
    mono_ctx_vars = [(vn, vt) for (vn, vt) in ctx_vars if not isinstance(vt, TypePolymorphism)]

    # Strip refinements from monomorphic variable types
    ctx_vars_unrefined = [(var_name, refined_to_unrefined_type(var_ty)) for (var_name, var_ty) in mono_ctx_vars]

    # Collect types that are used as type arguments to parameterized constructors.
    # These are the only types we need to instantiate forall-bound variables with.
    # For example, in `List Chunk`, `Chunk` is a type argument.
    instantiation_types: set[TypeConstructor] = set()
    for _, vt in mono_ctx_vars:
        _collect_type_arg_types(vt, instantiation_types)
    _collect_type_arg_types(ty, instantiation_types)

    # Monomorphize polymorphic variables
    monomorphized: list[tuple[Name, Type, list[Type]]] = []
    for vn, vt in poly_ctx_vars:
        for mono_body, type_apps in monomorphize_poly_type(vt, instantiation_types):
            mono_body_unrefined = refined_to_unrefined_type(mono_body)
            monomorphized.append((vn, mono_body_unrefined, type_apps))

    # Collect types from monomorphized vars
    mono_extra_types: set[Type] = set()
    for _, mt, _ in monomorphized:
        mono_extra_types.add(mt)

    # Build set of all types to consider
    types_to_consider = (
        set([t_bool, t_float, t_int, t_string]) | set([x[1] for x in ctx_vars_unrefined]) | set([ty]) | mono_extra_types
    )
    types_to_consider = types_to_consider - set(TypeConstructor(t) for t in types_to_ignore)
    type_info = extract_all_types(list(types_to_consider))
    type_nodes = list(set(type_info.values()))

    literals = create_literals_nodes(type_info)
    vars = create_var_nodes(ctx_vars_unrefined, type_info)
    abstractions = create_abstraction_nodes(type_info)
    applications = create_application_nodes(type_info)
    literals_ref = create_literal_ref_nodes(type_info)
    ifs = create_if_nodes(type_info)
    mono_nodes = create_monomorphized_var_nodes(monomorphized, type_info)

    ret = type_nodes + literals + literals_ref + vars + applications + abstractions + mono_nodes
    if mangle_name(synth_func_name) in metadata and "disable_control_flow" in metadata[synth_func_name]:
        ret = ret + ifs
    # Use the unrefined base type as the grammar starting node.
    # Refined type metahandler literals are direct alternatives for the base class,
    # so no refined abstract class is needed as a starting symbol.
    return ret, type_info[refined_to_unrefined_type(ty)]


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
