from __future__ import annotations

import ast
import pathlib
from typing import Callable

from lark import Lark, Transformer, v_args
from lark.lark import PostLex
from lark.lexer import Token

from aeon.core.multiplicity import from_token, Multiplicity, MOmega
from aeon.core.types import Kind
from aeon.sugar.program import (
    Decorator,
    SAbstraction,
    SAnonConstructor,
    SAnnotation,
    SApplication,
    SQualifiedVar,
    SRefinementAbstraction,
    SRefinementApplication,
    SMatch,
    SMatchBranch,
    SMethodSelector,
    SHole,
    SBy,
    SIf,
    SLet,
    SLiteral,
    SRec,
    STerm,
    STypeAbstraction,
    STypeApplication,
    SVar,
)
from aeon.sugar.program import Definition
from aeon.sugar.program import ImportAe
from aeon.sugar.program import Program
from aeon.sugar.program import TypeDecl
from aeon.sugar.program import InductiveDecl
from aeon.sugar.program import ClassDecl, ClassMethod, InstanceDecl, InstanceMethod
from aeon.sugar.stypes import (
    SAbstractionType,
    SType,
    STypeConstructor,
    STypeVar,
    SRefinedType,
    STypePolymorphism,
    SRefinementPolymorphism,
)

from aeon.sugar.ast_helpers import i0
from aeon.sugar.ast_helpers import st_int, st_bool, st_string, st_float, st_unit
from aeon.sugar.stypes import builtin_types
from aeon.utils.name import Name, fresh_counter

from aeon.utils.location import FileLocation, Location


def ensure_list(a):
    if isinstance(a, list):
        return a
    else:
        return [a]


def _split_arg_multiplicities(fn_args):
    """Each entry in ``fn_args`` is one of:
      * a ``(name, type)`` 2-tuple from the plain-arg productions,
      * a ``(name, type, multiplicity)`` 3-tuple from ``mult_arg``, or
      * a ``(name, type, multiplicity, is_instance)`` 4-tuple from
        ``instance_arg``.
    Return a list of 2-tuples plus parallel tuples of multiplicities
    (defaulting to ``MOmega``) and instance flags (defaulting to ``False``)."""
    plain: list = []
    mults: list[Multiplicity] = []
    flags: list[bool] = []
    for a in fn_args:
        if isinstance(a, tuple) and len(a) == 4:
            plain.append((a[0], a[1]))
            mults.append(a[2])
            flags.append(a[3])
        elif isinstance(a, tuple) and len(a) == 3:
            plain.append((a[0], a[1]))
            mults.append(a[2])
            flags.append(False)
        else:
            plain.append(a)
            mults.append(MOmega)
            flags.append(False)
    return plain, tuple(mults), tuple(flags)


# Token types that can end a method-call *receiver*. An immediately-following
# ``.name`` (no intervening whitespace) is then a method dot, Lean-style — not an
# anonymous constructor. (Bare ``x.name`` never reaches here: the lexer already
# fuses it into a single ``QUALIFIED_ID``.)
_RECEIVER_END_TOKENS = frozenset(
    {
        "RPAR",  # (e).m
        "INTLIT",  # 1.m
        "FLOATLIT",  # 1.5.m
        "BOOLLIT",
        "ESCAPED_STRING",
        "ID",  # ?x.m (hole) and any bare ident not fused into QUALIFIED_ID
        "QUALIFIED_ID",  # x.a.m  -> (x.a).m
        "METHOD_DOT",  # 1.a.b chains
    }
)


class MethodDotPostLex(PostLex):
    """Distinguish a method/projection dot from an anonymous-constructor dot by
    whitespace, mirroring Lean (issue #27).

    A ``DOT_ID`` (``.name``) that is *attached* to the previous token — no
    whitespace, and that token can end a receiver — is retagged ``METHOD_DOT``
    and binds tighter than application (``f 1.toString`` ≡ ``f (1.toString)``).
    A leading or space-separated ``.name`` stays a ``DOT_ID`` anonymous
    constructor (``.mk .sc_blue 40``)."""

    # Ensure the contextual LALR lexer always offers ``DOT_ID`` (``METHOD_DOT``
    # has no pattern; it is produced only here), so attached dots are lexable in
    # states that expect a method dot.
    always_accept = ("DOT_ID",)

    def process(self, stream):
        prev: Token | None = None
        for tok in stream:
            if (
                tok.type == "DOT_ID"
                and prev is not None
                and prev.type in _RECEIVER_END_TOKENS
                and prev.end_pos is not None
                and tok.start_pos is not None
                and prev.end_pos == tok.start_pos
            ):
                tok.type = "METHOD_DOT"
            prev = tok
            yield tok


class AnnotatedStr(str):
    loc: Location

    def __init__(self, value: str, loc: Location):
        self.loc = loc


class TreeToSugar(Transformer):
    filename: str
    counter: int

    def __init__(self, filename: str, start_counter: int = 0):
        self.filename = filename
        self.counter = start_counter

    def _loc(self, meta):
        return FileLocation(self.filename, start=(meta.line, meta.column), end=(meta.end_line, meta.end_column))

    def same(self, args):
        return args[0]

    # Types
    def refined_t(self, args):
        return SRefinedType(Name(args[0]), args[1], args[2])

    def abstraction_t(self, args):
        return SAbstractionType(Name(args[0]), args[1], args[2])

    def polymorphism_t(self, args):
        return STypePolymorphism(Name(args[0]), args[1], args[2])

    def pred_sort(self, args):
        # The sort of an abstract-refinement parameter, parsed as a bare arrow
        # chain ``d1 -> d2 -> ... -> Bool``. Fold it (right-associatively) into
        # the curried predicate type, which is stored directly as the
        # refinement's ``sort``. Unary ``d -> Bool`` yields ``SAbstractionType(d,
        # Bool)``; binary ``d -> d -> Bool`` yields ``d -> (d -> Bool)``; etc.
        domains = list(args[:-1])
        sort: SType = args[-1]
        for d in reversed(domains):
            sort = SAbstractionType(Name("_"), d, sort)
        return sort

    def refinement_polymorphism_t(self, args):
        return SRefinementPolymorphism(Name(args[0]), args[1], args[2])

    def base_angle_refined_t(self, args):
        base_str = str(args[0])
        pred_str = str(args[1])
        if base_str in builtin_types:
            base_ty = STypeConstructor(Name(base_str, 0))
        else:
            base_ty = STypeVar(Name(base_str))
        binder = Name(f"_r{fresh_counter.fresh()}")
        refinement = SApplication(SVar(Name(pred_str)), SVar(binder))
        return SRefinedType(binder, base_ty, refinement)

    def simple_t(self, args):
        name_str = str(args[0])
        if name_str in builtin_types:
            name = Name(name_str, 0)
            return STypeConstructor(name)
        else:
            name = Name(name_str)
            return STypeVar(name)

    def constructor_t(self, args):
        return STypeConstructor(Name(args[0]), args[1:])

    # Expressions
    @v_args(meta=True)
    def annotation(self, meta, args):
        return SAnnotation(args[0], args[1], loc=self._loc(meta))

    @v_args(meta=True)
    def minus(self, meta, args):
        if isinstance(args[0], SLiteral) and type(args[0].value) is int:
            return SLiteral(-args[0].value, args[0].type, loc=self._loc(meta))
        return self.binop([i0, args[0]], "-", meta)

    @v_args(meta=True)
    def let_e(self, meta, args):
        return SLet(Name(args[0]), args[1], args[2], loc=self._loc(meta))

    @v_args(meta=True)
    def mult_let_e(self, meta, args):
        # `let MULT ID = value in body`
        return SLet(Name(args[1]), args[2], args[3], loc=self._loc(meta), multiplicity=from_token(str(args[0])))

    @v_args(meta=True)
    def rec_e(self, meta, args):
        return SRec(Name(args[0]), args[1], args[2], args[3], decreasing_by=(), loc=self._loc(meta))

    @v_args(meta=True)
    def mult_rec_e(self, meta, args):
        # `let MULT ID : type = value in body`
        return SRec(
            Name(args[1]),
            args[2],
            args[3],
            args[4],
            decreasing_by=(),
            loc=self._loc(meta),
            multiplicity=from_token(str(args[0])),
        )

    @v_args(meta=True)
    def rec_refined_e(self, meta, args):
        name = Name(args[0])
        refined_type = SRefinedType(name, args[1], args[2])
        return SRec(name, refined_type, args[3], args[4], decreasing_by=(), loc=self._loc(meta))

    @v_args(meta=True)
    def mult_rec_refined_e(self, meta, args):
        # `let MULT ID : type | refinement = value in body`
        name = Name(args[1])
        refined_type = SRefinedType(name, args[2], args[3])
        return SRec(
            name,
            refined_type,
            args[4],
            args[5],
            decreasing_by=(),
            loc=self._loc(meta),
            multiplicity=from_token(str(args[0])),
        )

    @v_args(meta=True)
    def if_e(self, meta, args):
        return SIf(args[0], args[1], args[2], loc=self._loc(meta))

    def TACTIC_CMD(self, tok):
        return str(tok)

    def tactic_steps(self, args):
        return tuple(s for s in args if s != ";")

    def by_body_atomic(self, args):
        return (args[0],)

    def by_body_paren(self, args):
        return args[0]

    @v_args(meta=True)
    def by_e(self, meta, args):
        steps = args[0]
        assert isinstance(steps, tuple)
        return SBy(steps, loc=self._loc(meta))

    @v_args(meta=True)
    def match_e(self, meta, args):
        # match <scrutinee> with <branches>
        return SMatch(args[0], args[1], loc=self._loc(meta))

    @v_args(meta=True)
    def match_branch(self, meta, args):
        # | <Constructor> <binders>* => <body>
        constructor_name = Name(args[0])
        binders = [Name(b) for b in args[1]]
        return SMatchBranch(constructor=constructor_name, binders=binders, body=args[2], loc=self._loc(meta))

    @v_args(meta=True)
    def match_branch_qualified(self, meta, args):
        # | Type.Constructor <binders>* => <body>
        parts = str(args[0]).split(".", 1)
        qualifier = parts[0]
        constructor_name = Name(parts[1])
        binders = [Name(b) for b in args[1]]
        return SMatchBranch(
            constructor=constructor_name, binders=binders, body=args[2], qualifier=qualifier, loc=self._loc(meta)
        )

    @v_args(meta=True)
    def match_branch_anon(self, meta, args):
        # | .Constructor <binders>* => <body>
        bare = str(args[0])[1:]  # strip leading dot
        constructor_name = Name(bare)
        binders = [Name(b) for b in args[1]]
        return SMatchBranch(constructor=constructor_name, binders=binders, body=args[2], loc=self._loc(meta))

    @v_args(meta=True)
    def anon_constructor(self, meta, args):
        bare = str(args[0])[1:]  # strip leading dot
        return SAnonConstructor(bare, loc=self._loc(meta))

    @v_args(meta=True)
    def nnot(self, meta, args):
        return SApplication(SVar(Name("!", 0), loc=self._loc(meta)), args[0], loc=self._loc(meta))

    @v_args(meta=True)
    def binop_eq(self, meta, args):
        return self.binop(args, "==", meta)

    @v_args(meta=True)
    def binop_neq(self, meta, args):
        return self.binop(args, "!=", meta)

    @v_args(meta=True)
    def binop_and(self, meta, args):
        return self.binop(args, "&&", meta)

    @v_args(meta=True)
    def binop_or(self, meta, args):
        return self.binop(args, "||", meta)

    @v_args(meta=True)
    def binop_lt(self, meta, args):
        return self.binop(args, "<", meta)

    @v_args(meta=True)
    def binop_le(self, meta, args):
        return self.binop(args, "<=", meta)

    @v_args(meta=True)
    def binop_gt(self, meta, args):
        return self.binop(args, ">", meta)

    @v_args(meta=True)
    def binop_ge(self, meta, args):
        return self.binop(args, ">=", meta)

    @v_args(meta=True)
    def binop_imp(self, meta, args):
        return self.binop(args, "-->", meta)

    @v_args(meta=True)
    def binop_plus(self, meta, args):
        return self.binop(args, "+", meta)

    @v_args(meta=True)
    def binop_minus(self, meta, args):
        return self.binop(args, "-", meta)

    @v_args(meta=True)
    def binop_mult(self, meta, args):
        return self.binop(args, "*", meta)

    @v_args(meta=True)
    def binop_div(self, meta, args):
        return self.binop(args, "/", meta)

    @v_args(meta=True)
    def binop_mod(self, meta, args):
        return self.binop(args, "%", meta)

    @v_args(meta=True)
    def binop_dollar(self, meta, args):
        # `$` is syntactic sugar for function application (right-associative by grammar).
        return SApplication(args[0], args[1], loc=self._loc(meta))

    def binop(self, args, op: str, meta):
        return SApplication(
            SApplication(SVar(Name(op, 0), loc=self._loc(meta)), args[0], loc=self._loc(meta)),
            args[1],
            loc=self._loc(meta),
        )

    @v_args(meta=True)
    def application_e(self, meta, args):
        return SApplication(args[0], args[1], loc=self._loc(meta))

    @v_args(meta=True)
    def method_access(self, meta, args):
        # ``receiver.method`` (issue #27). ``args[0]`` is the receiver expression
        # and ``args[1]`` is the ``DOT_ID`` token ``.method``. The receiver is the
        # *argument* of the selector so existing ``SApplication``-recursing passes
        # walk into it without needing a dedicated case.
        receiver = args[0]
        method = str(args[1])[1:]  # strip leading dot
        loc = self._loc(meta)
        return SApplication(SMethodSelector(Name(method), loc=loc), receiver, loc=loc)

    @v_args(meta=True)
    def abstraction_e(self, meta, args):
        return SAbstraction(Name(args[0]), args[1], loc=self._loc(meta))

    @v_args(meta=True)
    def tabstraction_e(self, meta, args):
        return STypeAbstraction(Name(args[0]), args[1], args[2], loc=self._loc(meta))

    @v_args(meta=True)
    def rabstraction_e(self, meta, args):
        return SRefinementAbstraction(Name(args[0]), args[1], args[2], loc=self._loc(meta))

    @v_args(meta=True)
    def type_application_e(self, meta, args):
        return STypeApplication(args[0], args[1], loc=self._loc(meta))

    @v_args(meta=True)
    def refinement_application_e(self, meta, args):
        return SRefinementApplication(args[0], args[1], loc=self._loc(meta))

    @v_args(meta=True)
    def var(self, meta, args):
        return SVar(Name(args[0]), loc=self._loc(meta))

    @v_args(meta=True)
    def qualified_var(self, meta, args):
        parts = str(args[0]).split(".", 1)
        return SQualifiedVar(parts[0], Name(parts[1]), loc=self._loc(meta))

    @v_args(meta=True)
    def hole(self, meta, args):
        return SHole(Name(args[0]), loc=self._loc(meta))

    @v_args(meta=True)
    def int_lit(self, meta, args):
        return SLiteral(int(args[0]), type=st_int, loc=self._loc(meta))

    @v_args(meta=True)
    def float_lit(self, meta, args):
        return SLiteral(float(args[0]), type=st_float, loc=self._loc(meta))

    @v_args(meta=True)
    def bool_lit(self, meta, args):
        value = str(args[0]) == "true"
        return SLiteral(value, type=st_bool, loc=self._loc(meta))

    @v_args(meta=True)
    def string_lit(self, meta, args):
        return SLiteral(args[0], type=st_string, loc=self._loc(meta))

    def ESCAPED_STRING(self, val):
        return ast.literal_eval(str(val))

    def base_kind(self, args):
        return Kind.BASE

    def star_kind(self, args):
        return Kind.STAR

    def list(self, args):
        return args

    def program(self, args):
        type_section, def_section = args[1], args[2]
        inductive = [el for el in type_section if isinstance(el, InductiveDecl)]
        classes = [el for el in type_section if isinstance(el, ClassDecl)]
        type_decls = [el for el in type_section if isinstance(el, TypeDecl)]
        definitions = [el for el in def_section if isinstance(el, Definition)]
        instances = [el for el in def_section if isinstance(el, InstanceDecl)]
        return Program(args[0], type_decls, inductive, definitions, classes, instances)

    # ------- Typeclasses -------

    def class_param(self, args):
        return (Name(args[0]), args[1])

    def class_supers(self, args):
        return list(args)

    @v_args(meta=True)
    def class_method(self, meta, args):
        return ClassMethod(Name(args[0]), [], args[1], default=None, loc=self._loc(meta))

    @v_args(meta=True)
    def class_method_default(self, meta, args):
        return ClassMethod(Name(args[0]), [], args[1], default=args[2], loc=self._loc(meta))

    @v_args(meta=True)
    def class_decl(self, meta, args):
        name, params, supers, members = args
        return ClassDecl(
            Name(name),
            type_params=list(params),
            supers=list(supers),
            methods=list(members),
            loc=self._loc(meta),
        )

    def inst_name_none(self, args):
        return None

    def inst_name_given(self, args):
        return Name(args[0])

    def constraint_type(self, args):
        return STypeConstructor(Name(str(args[0])), list(args[1]))

    def inst_constraint(self, args):
        return args[0]

    @v_args(meta=True)
    def instance_method(self, meta, args):
        name, binders, body = args[0], args[1], args[2]
        method_args = [(Name(b), None) for b in binders]
        return InstanceMethod(Name(name), method_args, body, loc=self._loc(meta))

    @v_args(meta=True)
    def instance_decl(self, meta, args):
        inst_name, constraints, class_tok, type_atoms, members = args
        return InstanceDecl(
            class_name=Name(str(class_tok)),
            type_args=list(type_atoms),
            constraints=list(constraints),
            methods=list(members),
            name=inst_name,
            loc=self._loc(meta),
        )

    def module_path(self, args):
        return ".".join(str(a) for a in args)

    @v_args(meta=True)
    def module_imp(self, meta, args):
        return ImportAe(args[0], loc=self._loc(meta))

    @v_args(meta=True)
    def module_selective_imp(self, meta, args):
        names = [str(n) for n in args[1]]
        return ImportAe(args[0], selected_names=names, loc=self._loc(meta))

    @v_args(meta=True)
    def open_imp(self, meta, args):
        return ImportAe(args[0], is_open=True, loc=self._loc(meta))

    @v_args(meta=True)
    def type_decl(self, meta, args):
        rforalls = ensure_list(args[1]) if len(args) > 1 else []
        return TypeDecl(Name(args[0]), [], rforalls, loc=self._loc(meta))

    @v_args(meta=True)
    def type_constructor_decl(self, meta, args):
        # Last arg is the (possibly empty) inductive_rforalls list; preceding args are the type params.
        rforalls = ensure_list(args[-1]) if len(args) > 1 else []
        return TypeDecl(Name(args[0]), [Name(i) for i in args[1:-1]], rforalls, loc=self._loc(meta))

    def inductive_rforall_binding(self, args):
        return (Name(args[0]), args[1])

    @v_args(meta=True)
    def inductive(self, meta, args):
        return InductiveDecl(
            Name(args[0]),
            [Name(i) for i in args[1]],
            ensure_list(args[2]),
            ensure_list(args[3]),
            ensure_list(args[4]),
            loc=self._loc(meta),
        )

    @v_args(meta=True)
    def def_ind_cons(self, meta, args):
        plain_args, mults, flags = _split_arg_multiplicities(args[1])
        return Definition(
            Name(args[0]),
            [],
            plain_args,
            args[2],
            SLiteral(None, st_unit),
            loc=self._loc(meta),
            arg_multiplicities=mults,
            instance_flags=flags,
        )

    def decreasing_by_none(self, args):
        return []

    def decreasing_exprs(self, args):
        return list(args)

    @v_args(meta=True)
    def decreasing_by_list(self, meta, args):
        return args[0]

    @v_args(meta=True)
    def def_fun(self, meta, args):
        if len(args) == 5:
            name, fn_args, rtype, decr, body = args
            plain_args, mults, flags = _split_arg_multiplicities(fn_args)
            return Definition(
                Name(name),
                [],
                plain_args,
                rtype,
                body,
                decreasing_by=ensure_list(decr),
                loc=self._loc(meta),
                arg_multiplicities=mults,
                instance_flags=flags,
            )
        if len(args) == 6:
            decorators, name, fn_args, rtype, decr, body = args
            plain_args, mults, flags = _split_arg_multiplicities(fn_args)
            return Definition(
                Name(name),
                [],
                plain_args,
                rtype,
                body,
                decorators,
                [],
                decreasing_by=ensure_list(decr),
                loc=self._loc(meta),
                arg_multiplicities=mults,
                instance_flags=flags,
            )
        raise AssertionError(f"def_fun: unexpected args {args!r}")

    @v_args(meta=True)
    def def_cons(self, meta, args):
        if len(args) == 3:
            return Definition(Name(args[0]), [], [], args[1], args[2], loc=self._loc(meta))
        else:
            decorators = args[0]
            return Definition(Name(args[1]), [], [], args[2], args[3], decorators, loc=self._loc(meta))

    @v_args(meta=True)
    def def_fun_eq(self, meta, args):
        return self.def_fun(meta, args)

    def macros(self, args):
        return args

    @v_args(meta=True)
    def macro(self, meta, args):
        name = Name(args[0])
        macro_args_raw = args[1]
        positional = [a for a in macro_args_raw if not isinstance(a, tuple)]
        named = {a[0]: a[1] for a in macro_args_raw if isinstance(a, tuple)}
        return Decorator(name, positional, named, loc=self._loc(meta))

    def macro_args(self, args):
        return args

    def named_macro_arg(self, args):
        return (Name(args[0]), args[1])

    def positional_macro_arg(self, args):
        return args[0]

    def empty_list(self, args):
        return []

    def args(self, args):
        return args

    def arg(self, args):
        return (Name(args[0]), args[1])

    def refined_arg(self, args):
        return Name(args[0]), SRefinedType(Name(args[0]), args[1], args[2])

    def mult_arg(self, args):
        # (MULT ID : type) — multiplicity-annotated parameter.
        # Returns a 3-tuple so def_fun can pick up the multiplicity.
        return (Name(args[1]), args[2], from_token(str(args[0])))

    def mult_refined_arg(self, args):
        # (MULT ID : type | refinement)
        ty = SRefinedType(Name(args[1]), args[2], args[3])
        return (Name(args[1]), ty, from_token(str(args[0])))

    def instance_arg(self, args):
        # [type] — instance-implicit dictionary parameter. The binder name is
        # synthesized; callers never write it (elaboration resolves it).
        ty = args[0]
        name = Name(f"_inst{fresh_counter.fresh()}")
        return (name, ty, MOmega, True)

    def abstraction_refined_t(self, args):
        type = SRefinedType(Name(args[0]), args[1], args[2])
        return SAbstractionType(Name(args[0]), type, args[3])

    def mult_abstraction_t(self, args):
        # (MULT ID : type) -> type
        return SAbstractionType(Name(args[1]), args[2], args[3], multiplicity=from_token(str(args[0])))

    def mult_abstraction_refined_t(self, args):
        # (MULT ID : type | refinement) -> type
        ty = SRefinedType(Name(args[1]), args[2], args[3])
        return SAbstractionType(Name(args[1]), ty, args[4], multiplicity=from_token(str(args[0])))

    def abstraction_et(self, args):
        return SAnnotation(
            SAbstraction(Name(args[0]), args[2]),
            SAbstractionType(Name(args[0]), args[1], STypeVar(Name("?t", fresh_counter.fresh()))),
        )


_parser_cache: dict[str, Lark] = {}


def _get_cached_parser(rule: str) -> Lark:
    if rule not in _parser_cache:
        _parser_cache[rule] = Lark.open(
            pathlib.Path(__file__).parent.absolute() / "aeon_sugar.lark",
            parser="lalr",
            start=rule,
            import_paths=[pathlib.Path(__file__).parent.parent.absolute() / "frontend"],
            propagate_positions=True,
            postlex=MethodDotPostLex(),
        )
    return _parser_cache[rule]


def mk_parser(rule="start", start_counter: int = 0, filename: str = ""):
    parser = _get_cached_parser(rule)
    transf = TreeToSugar(filename, start_counter)

    def parse(s: str):
        tree = parser.parse(s)
        return transf.transform(tree)

    return parse


parse_expression: Callable[[str], STerm] = mk_parser("expression")
parse_program: Callable[[str], Program] = mk_parser("program")
parse_type: Callable[[str], SType] = mk_parser("type", filename="<prelude>")


def parse_main_program(source: str, filename: str) -> Program:
    return mk_parser("program", filename=filename)(source)
