"""Lower ``class`` / ``instance`` declarations during desugaring."""

from __future__ import annotations

from aeon.core.types import Kinding
from aeon.core.types import Kind
from aeon.errors import TypeClassError
from aeon.sugar.ast_helpers import st_string, st_unit
from aeon.sugar.instance_registry import (
    ClassInfo,
    InstanceInfo,
    clear_instance_registry,
    infer_type_variable_kinds,
    register_class,
    register_instance,
)
from aeon.sugar.program import (
    ClassDecl,
    ClassMethod,
    Definition,
    InductiveDecl,
    InstanceMethod,
    Program,
    SAbstraction,
    SApplication,
    SLiteral,
    SQualifiedVar,
    STerm,
    STypeApplication,
    STypeAbstraction,
    SVar,
)
from aeon.sugar.stypes import SAbstractionType, SType, STypeConstructor, STypeVar, STypePolymorphism, get_type_vars
from aeon.utils.name import Name, fresh_counter


def _mangle_stype(ty: SType) -> str:
    """A flat identifier-safe rendering of a type, used to name instance dicts."""
    match ty:
        case STypeVar(name):
            return name.name
        case STypeConstructor(name, args):
            if not args:
                return name.name
            return name.name + "_" + "_".join(_mangle_stype(a) for a in args)
        case _:
            return "t"


def _stype_head_name(ty: SType) -> str | None:
    """Outermost type-constructor (or type-variable) name of a type, used to key
    the instance database. ``Int`` → "Int", ``List a`` → "List", ``a`` → "a"."""
    match ty:
        case STypeConstructor(name, _):
            return name.name
        case STypeVar(name):
            return name.name
        case _:
            return None


def _curry_lambda(binders: list[Name], body: STerm) -> STerm:
    """Wrap ``body`` in nested lambdas, one per binder (left-to-right)."""
    for b in reversed(binders):
        body = SAbstraction(b, body)
    return body


def expand_typeclasses(p: Program) -> Program:
    """Lower ``class``/``instance`` declarations to inductives + plain definitions.

    A ``class C (a : k) where m_i : T_i [:= d_i]`` becomes:
      * an inductive ``C a`` with a single constructor ``C_mk`` whose fields are
        the method types — dependent, so a later field's refinement may mention an
        earlier method (this is how refinement *laws* are encoded); and
      * one projection ``def m_i : forall a, [d : C a] -> T_i = native "d[i+1]"``
        that pulls field ``i`` out of the runtime dictionary tuple
        ``('C_mk', f0, f1, …)``.

    An ``instance [Ck a]… : C T where m_i bs := e_i`` becomes a dictionary
    definition ``def <name> : C T = C_mk impl_0 … impl_n`` where each ``impl_i``
    is the supplied body (curried over its binders) or the class default when the
    method is omitted. Instance constraints become instance-implicit parameters.
    """
    # The driver may desugar the complete program more than once in a session.
    clear_instance_registry()
    if not p.class_decls and not p.instance_decls:
        return p

    # Generated projection / dictionary definitions must precede user code that
    # references them: aeon resolves names define-before-use, so we prepend.
    new_inductives: list[InductiveDecl] = list(p.inductive_decls)
    gen_defs: list[Definition] = []

    class_methods: dict[str, list[ClassMethod]] = {}

    classes = {cls.name.name: cls for cls in p.class_decls}
    if len(classes) != len(p.class_decls):
        raise TypeClassError("Duplicate class declaration")
    ordered: list[ClassDecl] = []
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(cls: ClassDecl) -> None:
        name = cls.name.name
        if name in visiting:
            raise TypeClassError(f"Superclass cycle involving '{name}'", cls.loc)
        if name in visited:
            return
        visiting.add(name)
        for parent in cls.supers:
            if not isinstance(parent, STypeConstructor) or parent.name.name not in classes:
                raise TypeClassError(f"Unknown superclass '{parent}'", cls.loc)
            target = classes[parent.name.name]
            if len(parent.args) != len(target.type_params):
                raise TypeClassError(f"Wrong number of arguments for superclass '{target.name.name}'", cls.loc)
            visit(target)
        visiting.remove(name)
        visited.add(name)
        ordered.append(cls)

    for cls in p.class_decls:
        visit(cls)

    for cls in ordered:
        cname = cls.name
        type_param_names = [n for (n, _) in cls.type_params]
        class_methods[cname.name] = list(cls.methods)
        if len({m.name.name for m in cls.methods}) != len(cls.methods):
            raise TypeClassError(f"Duplicate method in class '{cname.name}'", cls.loc)
        super_fields = [(Name(f"__super_{cname.name}_{i}"), ty) for i, ty in enumerate(cls.supers)]
        register_class(cname.name, ClassInfo(tuple(cls.type_params), tuple(super_fields)))

        ret_type = STypeConstructor(cname, [STypeVar(n) for n in type_param_names])

        # Unprefixed constructor name ``mk``; ``expand_inductive_decls`` namespaces
        # it to ``<Class>_mk``. The dictionary is built by referencing it through
        # ``SQualifiedVar(<Class>, mk)`` (resolved per-class during desugaring).
        cons = Definition(
            name=Name("mk"),
            foralls=list(cls.type_params),
            args=super_fields + [(m.name, m.type) for m in cls.methods],
            type=ret_type,
            body=SLiteral(None, st_unit),
            loc=cls.loc,
            instance_flags=tuple(True for _ in super_fields) + tuple(False for _ in cls.methods),
        )
        new_inductives.append(
            InductiveDecl(
                name=cname,
                args=list(type_param_names),
                arg_kinds=tuple(k for _, k in cls.type_params),
                rforalls=[],
                constructors=[cons],
                measures=[],
                loc=cls.loc,
            )
        )

        foralls: list[tuple[Name, Kinding]] = [(n, k) for (n, k) in cls.type_params]
        for i, (projection, super_type) in enumerate(super_fields):
            dictionary = Name(f"_super_dict{fresh_counter.fresh()}")
            gen_defs.append(
                Definition(
                    name=projection,
                    foralls=list(foralls),
                    args=[(dictionary, ret_type)],
                    type=super_type,
                    body=SApplication(SVar(Name("native")), SLiteral(f"{dictionary.name}[{i + 1}]", st_string)),
                    loc=cls.loc,
                )
            )
        for i, m in enumerate(cls.methods, start=len(super_fields)):
            dict_name = Name(f"_d{fresh_counter.fresh()}")
            # Eta-expand the projection: peel the method type's leading arrows
            # into explicit ``args`` so the projection's *return* type is a base
            # (or refined) type rather than a function type. A ``native`` whose
            # return type is itself a polymorphic function type fails to
            # elaborate (the type-variable would be instantiated with a function
            # type, which cannot carry the inserted refinement). Applying the
            # dictionary field to the peeled binders sidesteps that entirely.
            peeled: list[tuple[Name, SType]] = []
            ret_t: SType = m.type
            method_foralls: list[tuple[Name, Kinding]] = []
            while isinstance(ret_t, STypePolymorphism):
                method_foralls.append((ret_t.name, ret_t.kind))
                ret_t = ret_t.body
            while isinstance(ret_t, SAbstractionType):
                peeled.append((ret_t.var_name, ret_t.var_type))
                ret_t = ret_t.type
            call = f"{dict_name.name}[{i + 1}]" + "".join(f"({pn.name})" for (pn, _) in peeled)
            gen_defs.append(
                Definition(
                    name=m.name,
                    foralls=list(foralls) + method_foralls,
                    args=[(dict_name, ret_type), *peeled],
                    type=ret_t,
                    body=SApplication(
                        SVar(Name("native", 0)),
                        SLiteral(call, st_string),
                    ),
                    loc=m.loc,
                    instance_flags=(True, *(False for _ in peeled)),
                )
            )

    def _concretize_head(ty: SType, bound: set[str]) -> SType:
        """Resolve a bare type name in an instance head to a constructor.

        The parser turns every non-builtin bare identifier into an
        ``STypeVar`` (it has no type registry), so ``instance : C Network``
        would otherwise be read as polymorphic over a variable *named*
        ``Network`` — making the method bodies see an abstract ``'Network``
        that won't unify with the concrete imported type. By Aeon's naming
        convention type variables are lower-case; an upper-case head name
        that is not bound by the instance's own constraints denotes a
        concrete type, so promote it to a (nullary) ``STypeConstructor``.
        Constraint-bound variables (e.g. ``a`` in ``instance [Eq a] : Eq
        (Box a)``) are preserved.
        """
        match ty:
            case STypeVar(name):
                if name.name not in bound and name.name[:1].isupper():
                    return STypeConstructor(name, [])
                return ty
            case STypeConstructor(name, args):
                return STypeConstructor(
                    name, [_concretize_head(a, bound) for a in args], loc=ty.loc, refinements=ty.refinements
                )
            case _:
                return ty

    # Superclass dictionaries must be in scope when constructing subclasses.
    class_order = {cls.name.name: i for i, cls in enumerate(ordered)}
    instance_names: set[str] = set()
    for instance_index, inst in enumerate(
        sorted(p.instance_decls, key=lambda inst: class_order.get(inst.class_name.name, -1))
    ):
        methods = class_methods.get(inst.class_name.name)
        if methods is None:
            raise TypeClassError(f"Instance for unknown class '{inst.class_name.name}'")

        # Variables genuinely bound by the instance (those appearing in its
        # constraints) stay variables; other upper-case head names are
        # concrete types. Rewrite the head args once and use throughout.
        constraint_vars: set[str] = set()
        for c in inst.constraints:
            constraint_vars |= {tv.name.name for tv in get_type_vars(c)}
        inst_type_args = [_concretize_head(ta, constraint_vars) for ta in inst.type_args]

        if len(inst_type_args) != len(classes[inst.class_name.name].type_params):
            raise TypeClassError(f"Wrong number of arguments for instance '{inst.class_name.name}'", inst.loc)
        provided: dict[str, InstanceMethod] = {m.name.name: m for m in inst.methods}
        if len(provided) != len(inst.methods):
            raise TypeClassError(f"Duplicate instance method in '{inst.class_name.name}'", inst.loc)
        extra = provided.keys() - {m.name.name for m in methods}
        if extra:
            raise TypeClassError(f"Unknown methods in '{inst.class_name.name}': {', '.join(sorted(extra))}", inst.loc)

        impls: list[STerm] = []
        for m in methods:
            im = provided.get(m.name.name)
            if im is not None:
                binders = [n for (n, _) in im.args]
                implementation = _curry_lambda(binders, im.body)
            elif m.default is not None:
                implementation = m.default
            else:
                raise TypeClassError(f"Instance of '{inst.class_name.name}' is missing method '{m.name.name}'")
            method_type = m.type
            parameters = []
            while isinstance(method_type, STypePolymorphism):
                parameters.append((method_type.name, method_type.kind))
                method_type = method_type.body
            for name, kind in reversed(parameters):
                implementation = STypeAbstraction(name, kind, implementation)
            impls.append(implementation)

        # Instantiate the dictionary constructor at the instance's type
        # arguments (e.g. ``Eq_mk[Int]``) so elaboration can resolve the
        # constructor's ``forall`` binders. The method implementations are
        # lambdas whose parameter types are unknown until ``a`` is fixed, so
        # argument-driven inference alone cannot recover it.
        dict_body: STerm = SQualifiedVar(inst.class_name.name, Name("mk"))
        for ta in inst_type_args:
            dict_body = STypeApplication(dict_body, ta)
        for impl in impls:
            dict_body = SApplication(dict_body, impl)

        dict_type: SType = STypeConstructor(inst.class_name, list(inst_type_args))

        tyvars = set()
        for ta in inst_type_args:
            tyvars |= get_type_vars(ta)
        for c in inst.constraints:
            tyvars |= get_type_vars(c)
        inferred_kinds = infer_type_variable_kinds([dict_type, *inst.constraints])
        inst_foralls: list[tuple[Name, Kinding]] = [
            (tv.name, inferred_kinds.get(tv.name, Kind.BASE)) for tv in sorted(tyvars, key=lambda t: t.name.name)
        ]

        constraint_args: list[tuple[Name, SType]] = [(Name(f"_c{fresh_counter.fresh()}"), c) for c in inst.constraints]

        if inst.name is not None:
            dict_def_name = inst.name
        else:
            # Rendered heads are readable but not injective (e.g. function
            # types or constructors whose names contain underscores).
            dict_def_name = Name(
                f"__inst_{inst.class_name.name}_{'_'.join(_mangle_stype(t) for t in inst_type_args)}_{instance_index}"
            )
        if dict_def_name.name in instance_names:
            raise TypeClassError(f"Duplicate instance name '{dict_def_name.name}'", inst.loc)
        instance_names.add(dict_def_name.name)

        gen_defs.append(
            Definition(
                name=dict_def_name,
                foralls=inst_foralls,
                args=constraint_args,
                type=dict_type,
                body=dict_body,
                loc=inst.loc,
                instance_flags=tuple(True for _ in constraint_args),
            )
        )

        register_instance(
            inst.class_name.name,
            InstanceInfo(
                dict_name=dict_def_name,
                foralls=tuple(n for (n, _) in inst_foralls),
                num_constraints=len(constraint_args),
                type_args=tuple(inst_type_args),
                constraints=tuple(inst.constraints),
            ),
        )

    return Program(
        p.imports,
        p.type_decls,
        new_inductives,
        gen_defs + list(p.definitions),
        p.class_decls,
        p.instance_decls,
        p.export_names,
        p.reexports,
    )
