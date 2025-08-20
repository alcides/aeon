from __future__ import annotations

# from loguru import logger
from aeon.utils.indented_logger import IndentedLogger
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.types import AbstractionType, BaseKind, Top, TypeConstructor
from aeon.core.types import Kind
from aeon.core.types import RefinedType
from aeon.core.types import StarKind
from aeon.core.types import t_bool
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.core.types import RefinimentPolymorphism
from aeon.core.types import TypeVar
from aeon.typechecking.context import TypingContext
from aeon.typechecking.liquid import typecheck_liquid


def wf_inner(
    ctx: TypingContext, t: Type, k: Kind = StarKind(), indentedlogger: IndentedLogger = IndentedLogger()
) -> bool:
    match t:
        case Top():
            indentedlogger.write("Top type is always wellformed")
            return True  # wf_no_refinement
        case RefinedType(name, TypeConstructor(_, _) as ty, refinement):
            indentedlogger.write(f"Checking wellformedness of {ty} with refinement {refinement}").indent("  ")
            inferred_type = typecheck_liquid(ctx.with_var(name, ty), refinement, indentedlogger=indentedlogger)
            indentedlogger.dedent().write(
                f"Wellformedness of {ty} with refinement {refinement}: {inferred_type == t_bool}"
            )
            return inferred_type == t_bool
        case TypeVar(tvname):
            indentedlogger.write(f"Checking wellformedness of type variable {tvname} with kind {k}").indent("  ")
            indentedlogger.write(f"Type variable {tvname} with kind {k} is wellformed: {(tvname, k) in ctx.typevars()}")
            indentedlogger.dedent()
            return tvname in [v[0] for v in ctx.typevars()]
        case RefinedType(name, TypeVar(tvname), LiquidLiteralBool(True)):
            indentedlogger.write(f"Checking wellformedness of type variable {tvname} with kind {k}").indent("  ")
            indentedlogger.write(
                f"Type variable {tvname} with kind {k} is wellformed: {(tvname, BaseKind()) in ctx.typevars()}"
            )
            indentedlogger.dedent()
            return (tvname, k) in ctx.typevars()
        case RefinedType(name, TypeVar(tvname) as ty, refinement):
            indentedlogger.write(
                f"Checking wellformedness of type variable {tvname} with refinement {refinement}"
            ).indent("  ")
            refinementtype = typecheck_liquid(ctx.with_var(name, ty), refinement, indentedlogger=indentedlogger)
            indentedlogger.dedent().write(
                f"Wellformedness of type variable {tvname} with refinement {refinement}: {refinementtype == t_bool}"
            )
            return k == BaseKind() and (tvname, BaseKind()) in ctx.typevars() and refinementtype == t_bool
        case AbstractionType(aname, atype, rtype):
            indentedlogger.write(
                f"Checking wellformedness of abstraction type {aname} : {atype} -> {rtype} with kind {k}"
            )
            wellformed_atype = wellformed(ctx, atype, indentedlogger=indentedlogger.indent("atype "))
            indentedlogger.dedent()
            wellformed_rtype = wellformed(
                ctx.with_var(aname, atype), rtype, indentedlogger=indentedlogger.indent("rtype ")
            )
            indentedlogger.dedent().write(
                f"Wellformedness of abstraction type {aname} : {atype} -> {rtype} with kind {k}: {wellformed_atype and wellformed_rtype}"
            )
            return k == StarKind() and wellformed_atype and wellformed_rtype
        case TypePolymorphism(name, kind, body):
            indentedlogger.write(
                f"Checking wellformedness of type polymorphism {name} : {kind} with body {body}"
            ).indent("  ")
            wellformedbody = wellformed(ctx.with_typevar(name, kind), body, indentedlogger=indentedlogger)
            indentedlogger.dedent().write(
                f"Wellformedness of type polymorphism {name} : {kind} with body {body}: {wellformedbody}"
            )
            return k == StarKind() and wellformedbody
        case RefinimentPolymorphism(name, kind, body):
            indentedlogger.write(
                f"Checking wellformedness of refinement polymorphism {name} : {kind} with body {body}"
            ).indent("  ")
            wellformedbody = wellformed(ctx.with_refinementvar(name, t), body, indentedlogger=indentedlogger)
            indentedlogger.dedent().write(
                f"Wellformedness of refinement polymorphism {name} : {kind} with body {body}: {wellformedbody}"
            )
            return k == StarKind() and wellformedbody
        case TypeConstructor(name, args):
            indentedlogger.write(f"Checking wellformedness of type constructor {name} with args {args}").indent("  ")
            if not args:
                indentedlogger.write(
                    f"Type constructor {name} with no args is wellformed: {ctx.get_type_constructor(name) is not None}"
                )
                indentedlogger.dedent()
                return ctx.get_type_constructor(name) is not None
            else:
                cargs = ctx.get_type_constructor(name)
                if not cargs or len(cargs) != len(args):
                    indentedlogger.write(
                        f"Type constructor {name} with args {args} is not wellformed: {cargs} != {args}"
                    )
                    indentedlogger.dedent()
                    return False
                indentedlogger.indent("  ")
                res = all(
                    wf_inner(ctx, t, indentedlogger=indentedlogger.dedent().indent(f"{i} ")) for i, t in enumerate(args)
                )
                indentedlogger.dedent().write(f"Type constructor {name} with args {args} is wellformed: {res}")
                return res
        case RefinedType(name, TypeConstructor(_, args) as ity, refinement):
            indentedlogger.write(f"Checking wellformedness of type constructor {ity} with refinement {refinement}")
            wity = wf_inner(ctx, ity, indentedlogger=indentedlogger.indent(" wity "))
            indentedlogger.dedent()
            typecheck_result = typecheck_liquid(
                ctx.with_var(name, ity), refinement, indentedlogger=indentedlogger.indent("typecheck ")
            )
            indentedlogger.dedent().write(
                f"Wellformedness of type constructor {ity} with refinement {refinement}: {wity and typecheck_result == t_bool}"
            )
            return wity and typecheck_result == t_bool
        case _:
            return False


def wellformed(
    ctx: TypingContext, t: Type, k: Kind = StarKind(), indentedlogger: IndentedLogger = IndentedLogger()
) -> bool:
    match k:
        case StarKind():
            indentedlogger.write(f"Checking wellformedness of {t} with ★").indent("  ")
            star = wf_inner(ctx, t, StarKind(), indentedlogger)
            base = wf_inner(ctx, t, BaseKind(), indentedlogger)
            indentedlogger.dedent().write(f"Wellformedness of {t} with ★: {star or base}")
            return star or base
        case _:
            indentedlogger.write(f"Checking wellformedness of {t} with {k}").indent("  ")
            base = wf_inner(ctx, t, BaseKind(), indentedlogger)
            indentedlogger.dedent().write(f"Wellformedness of {t} with {k}: {base}")
            return base
