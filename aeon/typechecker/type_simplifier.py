from ..types import TypingContext, Type, BasicType, RefinedType, AbstractionType, TypeAbstraction, \
    TypeApplication, SumType, IntersectionType, ProductType, Kind, AnyKind, star, TypeException, t_b, t_delegate, bottom, top
from ..ast import TypedNode, Application, Abstraction, TApplication, TAbstraction, Literal, Var, If, Hole

from .substitutions import substitution_expr_in_expr, substitution_type_in_type, substitution_expr_in_type
from .exceptions import TypingException

smt_true = Literal(True, t_b)
smt_and = lambda x, y: x == smt_true and y or (
    y == smt_true and x or Application(Application(Var("smtAnd"), x), y))
smt_or = lambda x, y: x == smt_true and smt_true or (
    y == smt_true and smt_true or Application(Application(Var("smtOr"), x), y))


def reduce_type(ctx: TypingContext, t: Type) -> Type:
    # Flatten refined types
    nt: Type

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
        else:
            return RefinedType(t.name, inner, t.cond)

    elif isinstance(t, AbstractionType):
        at = reduce_type(ctx, t.arg_type)
        rt = reduce_type(ctx, t.return_type)
        return AbstractionType(t.arg_name, at, rt)
    elif isinstance(t, TypeAbstraction):
        return TypeAbstraction(t.name, t.kind, reduce_type(ctx, t.type))
    elif isinstance(t, TypeApplication):
        tar = reduce_type(ctx, t.target)
        arg = reduce_type(ctx, t.argument)
        if isinstance(tar, TypeAbstraction):
            nt = substitution_type_in_type(tar.type, arg, tar.name)
            return reduce_type(ctx, nt)
        else:
            return TypeApplication(tar, arg)
    elif isinstance(t, SumType):
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
        else:
            return SumType(left, right)

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
            isinstance(right, BasicType) and \
                left.name == right.name:
            return left
        elif isinstance(left, RefinedType) and \
            isinstance(right, BasicType) and \
            left.type == right:
            return left
        elif isinstance(right, RefinedType) and \
            isinstance(left, BasicType) and \
            left == right.type:
            return right
        elif isinstance(right, RefinedType) and \
            isinstance(left, RefinedType) and \
                right.type == left.type:
            new_cond = smt_and(
                right.cond,
                substitution_expr_in_expr(left.cond, Var(right.name),
                                          left.name))
            return RefinedType(right.name, right.type, new_cond)
        else:
            return IntersectionType(left, right)
    elif isinstance(t, ProductType):
        left = reduce_type(ctx, t.left)
        right = reduce_type(ctx, t.right)
        return ProductType(t.left_name, left, right)
    raise TypingException("Simplifier missing rule:", type(t))
