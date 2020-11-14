from aeon.typechecker.unification import UnificationError
from typing import List, Optional
from aeon.free_variables import free_variables_in_type
from ..types import ExistentialType, TypingContext, Type, BasicType, RefinedType, AbstractionType, TypeAbstraction, \
    TypeApplication, UnionType, IntersectionType, ProductType, Kind, AnyKind, star, TypeException, t_b, t_delegate, bottom, top
from ..ast import TypedNode, Application, Abstraction, TApplication, TAbstraction, Literal, Var, If, Hole

from .substitutions import substitution_expr_in_expr, substitution_type_in_type, substitution_expr_in_type
from .exceptions import TypingException

smt_true = Literal(True, t_b)
smt_and = lambda x, y: x == smt_true and y or (
    y == smt_true and x or Application(Application(Var("smtAnd"), x), y))
smt_or = lambda x, y: x == smt_true and smt_true or (
    y == smt_true and smt_true or Application(Application(Var("smtOr"), x), y))


def reduce_type(ctx: TypingContext, t: Type, variables:Optional[List[str]] = None) -> Type:
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
        if isinstance(inner, RefinedType):
            new_cond = smt_and(
                t.cond,
                substitution_expr_in_expr(inner.cond, Var(t.name), inner.name))
            nt = RefinedType(t.name, inner.type, new_cond)
            return reduce_type(ctx, nt)
        elif isinstance(inner, BasicType) and t.cond == smt_true:
            return inner
        elif isinstance(inner, ExistentialType):
            return reduce_type(ctx, ExistentialType(inner.left_name, inner.left, RefinedType(t.name, inner.right, t.cond)))

        else:
            return RefinedType(t.name, inner, t.cond)

    elif isinstance(t, AbstractionType):
        at = reduce_type(ctx, t.arg_type)
        rt = reduce_type(ctx, t.return_type)
        return AbstractionType(t.arg_name, at, rt)
    elif isinstance(t, TypeAbstraction):
        # TODO: remove TypeAbstraction if variable esta linha está mal por causa das variáveis!
        return TypeAbstraction(t.name, t.kind, reduce_type(ctx, t.type, vars_in_ctx + [t.name]))
    elif isinstance(t, TypeApplication):
        tar = reduce_type(ctx, t.target)
        arg = reduce_type(ctx, t.argument)
        if isinstance(tar, TypeAbstraction):
            nt = substitution_type_in_type(tar.type, arg, tar.name)
            return reduce_type(ctx, nt)
        else:
            return TypeApplication(tar, arg)
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
        if isinstance(left, BasicType) and isinstance(right, RefinedType) and right.type == bottom:
            return RefinedType(right.name, left, right.cond)
        if isinstance(right, BasicType) and isinstance(left, RefinedType) and left.type == bottom:
            return RefinedType(left.name, right, left.cond)
        elif isinstance(right, ExistentialType):
            """ T + Ex:U.V -> Ex:U.V + T """
            nt = ExistentialType(right.left_name, right.left, UnionType(left, right.right))
            return reduce_type(ctx, nt)
        elif isinstance(left, ExistentialType):
            """ Ex:U.V + T -> Ex:U. (V + T) """
            nt = ExistentialType(left.left_name, left.left, UnionType(left.right, right))
            return reduce_type(ctx, nt)
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
            else:
                return bottom
        elif isinstance(left, RefinedType) and \
            isinstance(right, BasicType):
            if left.type == right:
                return left
            else:
                return bottom
        elif isinstance(right, RefinedType) and \
            isinstance(left, BasicType):
            if left == right.type:
                return right
            else:
                return bottom
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
            nt = ExistentialType(right.left_name, right.left, IntersectionType(left, right.right))
            return reduce_type(ctx, nt)
        elif isinstance(left, ExistentialType):
            """ Ex:U.V | T -> Ex:U. (V | T) """
            nt = ExistentialType(left.left_name, left.left, IntersectionType(left.right, right))
            return reduce_type(ctx, nt)
        elif isinstance(right, TypeAbstraction):
            from aeon.typechecker.unification import unificationEq, UnificationError
            try:
                k = unificationEq(ctx, left, right)
                return reduce_type(ctx, k)
            except UnificationError as e:
                raise e
                return bottom # TODO - check
            return IntersectionType(left, right)
        elif isinstance(left, TypeAbstraction):
            from aeon.typechecker.unification import unificationEq, UnificationError
            try:
                k = unificationEq(ctx, right, left)
                return reduce_type(ctx, k)

            except UnificationError:
                return bottom # TODO - check
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
        if isinstance(t.left, BasicType) and t.left_name not in free_variables_in_type(right):
            return right
        elif isinstance(t.left, RefinedType):
            """ Ex:{y:T | c}.U -> Ex:T.{k:U | c[x|y]}  """
            nr = RefinedType(ctx.fresh_var(), right, substitution_expr_in_expr(t.left.cond, Var(t.left_name), t.left.name))
            return reduce_type(ctx, ExistentialType(t.left_name, t.left.type, reduce_type(ctx, nr)))
        elif isinstance(t.left, ExistentialType):
            """ Ex:(Ey:Integer.T).U -> Ey:Integer.Ex:T.U """
            return reduce_type(ctx, ExistentialType(t.left.left_name, t.left.left, ExistentialType(t.left_name, t.left.right, t.right)))
        else:
            return ExistentialType(t.left_name, left, right)


    raise TypingException("Simplifier missing rule:", type(t))
