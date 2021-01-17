from typing import List, Optional

from ..typechecker.unification import UnificationError
from ..free_variables import free_variables_in_type
from ..types import ExistentialType, TypingContext, Type, BasicType, RefinedType, AbstractionType, TypeAbstraction, \
    TypeApplication, UnionType, IntersectionType, ProductType, Kind, AnyKind, apply_rec, find_basic_types, star, TypeException, t_b, t_delegate, bottom, top, type_map
from ..ast import TypedNode, Application, Abstraction, TApplication, TAbstraction, Literal, Var, If, Hole
from ..typechecker.ast_helpers import smt_true, smt_and, smt_eq, smt_or

from .substitutions import substitution_expr_in_expr, substitution_type_in_type, substitution_expr_in_type
from .exceptions import TypingException


def further_reduce_type(ctx: TypingContext, t: Type):
    from ..simplification import cnf_simplify, remove_eqs
    return apply_rec(
        lambda x: isinstance(x, RefinedType), lambda rec, x: RefinedType(
            x.name, rec(x.type),
            cnf_simplify(remove_eqs(cnf_simplify(x.cond), [x.name]))), t)


def reduce_type(ctx: TypingContext,
                t: Type,
                variables: Optional[List[str]] = None) -> Type:
    # Flatten refined types
    nt: Type

    if not variables:
        vars_in_ctx = []
    else:
        vars_in_ctx = variables

    if isinstance(t, BasicType):
        return t

    if isinstance(t, RefinedType):
        inner = reduce_type(ctx, t.type)
        t_cond = t.cond
        if isinstance(inner, RefinedType):
            new_cond = smt_and(
                t_cond,
                substitution_expr_in_expr(inner.cond, Var(t.name), inner.name))
            nt = RefinedType(t.name, inner.type, new_cond)
            return reduce_type(ctx, nt)
        elif isinstance(inner, BasicType) and t_cond == smt_true:
            return inner
        elif isinstance(inner, ExistentialType):
            return reduce_type(
                ctx,
                ExistentialType(inner.left_name, inner.left,
                                RefinedType(t.name, inner.right, t_cond)))

        else:
            return RefinedType(t.name, inner, t_cond)

    elif isinstance(t, AbstractionType):
        n_arg_name = t.arg_name + "_abs_" + ctx.fresh_var()
        at = reduce_type(ctx, t.arg_type)
        rt = reduce_type(
            ctx,
            substitution_expr_in_type(t.return_type, Var(n_arg_name),
                                      t.arg_name))
        return AbstractionType(n_arg_name, at, rt)
    elif isinstance(t, TypeAbstraction):
        rt = reduce_type(ctx, t.type, vars_in_ctx + [t.name])
        if t.name not in find_basic_types(rt) and t.name in vars_in_ctx:
            return rt
        return TypeAbstraction(t.name, t.kind, rt)
    elif isinstance(t, TypeApplication):
        tar = reduce_type(ctx, t.target)
        arg = reduce_type(ctx, t.argument)
        if isinstance(tar, TypeAbstraction):
            nt = substitution_type_in_type(tar.type, arg, tar.name)
            o = reduce_type(ctx, nt)
            return o
        elif isinstance(tar, BasicType) or isinstance(tar, TypeApplication):
            return TypeApplication(tar, arg)
        else:
            return tar  # TODO: check if this is correct
    elif isinstance(t, UnionType):
        left = reduce_type(ctx, t.left)
        right = reduce_type(ctx, t.right)
        if left == bottom:
            return right
        elif right == bottom:
            return left
        elif left == top or right == top:
            return top
        elif isinstance(left, BasicType) and \
            isinstance(right, BasicType) and \
                left.name == right.name:
            return left
        elif isinstance(left, RefinedType) and \
            isinstance(right, BasicType) and \
            left.type == right:
            return right
        elif isinstance(right, RefinedType) and \
            isinstance(left, BasicType) and \
            left == right.type:
            return left
        elif isinstance(right, RefinedType) and \
            isinstance(left, RefinedType) and \
                right.type == left.type:
            new_cond = smt_or(
                right.cond,
                substitution_expr_in_expr(left.cond, Var(right.name),
                                          left.name))
            return RefinedType(right.name, right.type, new_cond)
        if isinstance(left, BasicType) and isinstance(
                right, RefinedType) and right.type == bottom:
            return RefinedType(right.name, left, right.cond)
        if isinstance(right, BasicType) and isinstance(
                left, RefinedType) and left.type == bottom:
            return RefinedType(left.name, right, left.cond)
        elif isinstance(right, ExistentialType):
            """ T + Ex:U.V -> Ex:U.V + T """
            nt = ExistentialType(right.left_name, right.left,
                                 UnionType(left, right.right))
            return reduce_type(ctx, nt)
        elif isinstance(left, ExistentialType):
            """ Ex:U.V + T -> Ex:U. (V + T) """
            nt = ExistentialType(left.left_name, left.left,
                                 UnionType(left.right, right))
            return reduce_type(ctx, nt)
        elif isinstance(left, TypeAbstraction):
            n = UnionType(left.type, right)
            return reduce_type(ctx, TypeAbstraction(left.name, left.kind, n))
        elif isinstance(right, TypeAbstraction):
            n = UnionType(left, right.type)
            return reduce_type(ctx, TypeAbstraction(right.name, right.kind, n))
        else:
            return UnionType(left, right)

    elif isinstance(t, IntersectionType):
        left = reduce_type(ctx, t.left)
        right = reduce_type(ctx, t.right)
        if left == top:
            return right
        elif right == top:
            return left
        elif left == bottom or right == bottom:
            return bottom
        elif isinstance(left, BasicType) and \
            isinstance(right, BasicType):
            if left.name == right.name:
                return left
            elif left.name not in vars_in_ctx and right.name not in vars_in_ctx:
                return bottom
            else:
                return IntersectionType(left, right)
        elif isinstance(left, RefinedType) and \
            isinstance(right, BasicType):
            if left.type == right:
                return left
            else:
                return IntersectionType(left, right)
        elif isinstance(right, RefinedType) and \
            isinstance(left, BasicType):
            if left == right.type:
                return right
            else:
                return IntersectionType(left, right)
        elif isinstance(right, RefinedType) and \
            isinstance(left, RefinedType) and \
                right.type == left.type:
            new_cond = smt_and(
                right.cond,
                substitution_expr_in_expr(left.cond, Var(right.name),
                                          left.name))
            return RefinedType(right.name, right.type, new_cond)
        elif isinstance(right, ExistentialType):
            """ T | Ex:U.V -> Ex:U.V | T """
            nt = ExistentialType(right.left_name, right.left,
                                 IntersectionType(left, right.right))
            return reduce_type(ctx, nt)
        elif isinstance(left, ExistentialType):
            """ Ex:U.V | T -> Ex:U. (V | T) """
            nt = ExistentialType(left.left_name, left.left,
                                 IntersectionType(left.right, right))
            return reduce_type(ctx, nt)
        elif isinstance(right, TypeAbstraction) or isinstance(
                left, TypeAbstraction):
            from aeon.typechecker.unification import unificationEq, UnificationError
            try:
                k = unificationEq(ctx, right, left)
                return reduce_type(ctx, k)

            except UnificationError as e:
                return IntersectionType(left, right)
        else:
            return IntersectionType(left, right)
    elif isinstance(t, ProductType):
        left = reduce_type(ctx, t.left)
        right = reduce_type(ctx, t.right)
        return ProductType(t.left_name, left, right)
    elif isinstance(t, ExistentialType):
        left = reduce_type(ctx, t.left)
        right = reduce_type(ctx, t.right)
        if isinstance(t.left, BasicType
                      ) and t.left_name not in free_variables_in_type(right):
            return right
        elif isinstance(t.left, RefinedType):
            """ Ex:{y:T | c}.U -> Ex:T.{k:U | c[x|y]}  """
            n_left_name = t.left_name.split("_#")[0] + ctx.fresh_var()
            nright = substitution_expr_in_type(right, Var(n_left_name),
                                               t.left_name)

            nr = RefinedType(
                ctx.fresh_var(), nright,
                substitution_expr_in_expr(t.left.cond, Var(n_left_name),
                                          t.left.name))
            return reduce_type(
                ctx,
                ExistentialType(n_left_name, t.left.type, reduce_type(ctx,
                                                                      nr)))
        elif isinstance(t.left, ExistentialType):
            """ Ex:(Ey:Integer.T).U -> Ey:Integer.Ex:T.U """
            n_left_name = t.left_name.split("_#")[0] + ctx.fresh_var()
            nright = substitution_expr_in_type(right, Var(n_left_name),
                                               t.left_name)
            n_left_left_name = t.left.left_name.split(
                "_#")[0] + ctx.fresh_var()
            r = substitution_expr_in_type(t.left.right, Var(n_left_left_name),
                                          t.left.left_name)
            return reduce_type(
                ctx,
                ExistentialType(n_left_left_name, t.left.left,
                                ExistentialType(n_left_name, r, nright)))
        elif isinstance(t.left, TypeAbstraction):
            n_left_name = t.left_name.split("_#")[0] + ctx.fresh_var()
            nright = substitution_expr_in_type(right, Var(n_left_name),
                                               t.left_name)
            n_name = t.left.name + ctx.fresh_var()
            n_type = substitution_type_in_type(t.left.type, BasicType(n_name),
                                               t.left.name)
            return reduce_type(
                ctx,
                TypeAbstraction(n_name, t.left.kind,
                                ExistentialType(n_left_name, n_type, nright)))
        else:
            return ExistentialType(t.left_name, left, right)
    raise TypingException("Simplifier missing rule:", type(t), t)


def strong_reduce(ctx: TypingContext, t: Type):
    current = t
    next = reduce_type(ctx, t)
    next = further_reduce_type(ctx, next)
    while next != current:
        current = next
        next = further_reduce_type(ctx, current)
        next = reduce_type(ctx, next)
    return next
