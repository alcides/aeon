from ..types import Type, BasicType, RefinedType, AbstractionType, TypeApplication, TypeAbstraction, TypeException, t_b
from ..ast import TypedNode, Application, Abstraction, TApplication, TAbstraction, Literal, Var, If, Hole

from .substitutions import substitution_expr_in_expr, substitution_type_in_type, substitution_expr_in_type
from .exceptions import TypingException

smt_true = Literal(True, t_b)
smt_and = lambda x, y: x == smt_true and y or (
    y == smt_true and x or Application(Application(Var("smtAnd"), x), y))

remove_name = lambda name, lst: list(filter(lambda y: y[0] != name, lst))


class Result(object):
    def __init__(self,
                 expression=smt_true,
                 type=None,
                 extra_condition=smt_true,
                 should_abort=False,
                 variables=None):
        self.expression = expression
        self.type = type
        self.extra_condition = extra_condition
        self.should_abort = should_abort
        self.variables = variables or []

    def __repr__(self):
        return repr(self.expression) + " | " + repr(self.type) + " | " + repr(
            self.extra_condition) + " | " + repr(self.should_abort)


def liquefy_expr(ctx, n):
    if isinstance(n, Literal):
        r = liquefy_type(ctx, n.type)
        return Result(expression=Literal(n.value, r.type), type=r.type)
    elif isinstance(n, Var):
        if n.name in ctx.uninterpreted_functions.keys():
            return Result(expression=n,
                          type=ctx.uninterpreted_functions[n.name])
        else:
            ty = ctx.variables[n.name]
            r = liquefy_type(ctx, ty)
            if isinstance(r.type, BasicType):
                return Result(expression=n,
                              type=r.type,
                              extra_condition=substitution_expr_in_expr(
                                  r.extra_condition, Var(n.name),
                                  r.expression.name),
                              variables=r.variables)
            elif isinstance(r.type, AbstractionType):
                return Result(expression=r.expression,
                              type=r.type,
                              extra_condition=r.extra_condition,
                              should_abort=True,
                              variables=r.variables)
            else:
                raise Exception("not implemented yet!")
    elif isinstance(n, If):
        raise Exception("not implemented yet: if")
    elif isinstance(n, Application):
        t = liquefy_expr(ctx, n.target)
        a = liquefy_expr(ctx, n.argument)
        is_unliquid = t.should_abort or a.should_abort
        print("target,", n, t)
        new_type = t.type.return_type
        if not a.should_abort:
            new_type = substitution_expr_in_type(new_type, a.expression,
                                                 t.type.arg_name)
            t.extra_condition = substitution_expr_in_expr(
                t.extra_condition, a.expression, t.type.arg_name)
        nvariables = t.variables + a.variables  # TODO
        print(n, "...")
        print(t)
        print(a)
        return Result(expression=Application(t.expression, a.expression)
                      if not t.should_abort else t.expression.body,
                      type=new_type,
                      should_abort=t.should_abort,
                      extra_condition=smt_and(t.extra_condition,
                                              a.extra_condition),
                      variables=nvariables)
    elif isinstance(n, Abstraction):
        raise Exception("not implemented yet: lambda")
    elif isinstance(n, TApplication):
        return liquefy_expr(ctx, n.target)
    elif isinstance(n, TAbstraction):
        raise Exception("not implemented yet: tabstraction")
    elif isinstance(n, Hole):
        raise Exception("not implemented yet: hole")


def liquefy_type(ctx, ty):
    if isinstance(ty, BasicType):
        return Result(expression=Var("__useless__"), type=ty)
    elif isinstance(ty, RefinedType):
        nctx = ctx.with_var(ty.name, ty.type)
        rt = liquefy_type(nctx, ty.type)
        re = liquefy_expr(nctx, ty.cond)
        rt_cond = substitution_expr_in_expr(rt.extra_condition, Var(ty.name),
                                            rt.expression.name)
        re_cond = re.extra_condition
        nvariables = rt.variables + re.variables + [(ty.name, rt.type)]
        if re.should_abort:
            re_cond = substitution_expr_in_expr(re_cond, Var(ty.name),
                                                re.expression.name)
        new_condition = smt_and(rt_cond, re_cond)
        if not re.should_abort:
            new_condition = smt_and(new_condition, re.expression)
        return Result(expression=Var(ty.name),
                      extra_condition=new_condition,
                      type=rt.type,
                      variables=nvariables)

    elif isinstance(ty, AbstractionType):
        b = liquefy_type(ctx.with_var(ty.arg_name, ty.arg_type),
                         ty.return_type)
        return Result(
            expression=Abstraction(ty.arg_name, t_b, b.expression),
            type=AbstractionType(ty.arg_name, ty.arg_type, b.type),
            extra_condition=b.extra_condition,
            variables=b.variables,
        )

    elif isinstance(ty, TypeApplication) and isinstance(
            ty.target, TypeAbstraction):
        return liquefy_type(
            substitution_type_in_type(ty.target.body, ty.argument, ty.name))

    elif isinstance(ty, TypeApplication):
        return liquefy_type(ctx, ty.target)

    elif isinstance(ty, TypeAbstraction):
        return liquefy_type(ctx, ty.type)


def liquefy(ctx, ty):
    res = liquefy_type(ctx, ty)
    print(ty, res)
    if res.expression.name == '__useless__' or res.extra_condition == smt_true:
        return res.type
    ncond = res.extra_condition
    for (v, t) in remove_name(res.expression.name, res.variables):
        ncond = Application(Var('smt_exists'), Abstraction(v, t, ncond))
    print("Ncond:", ncond)
    return RefinedType(res.expression.name, res.type, ncond)
