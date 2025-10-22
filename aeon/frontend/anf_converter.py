from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    If,
    Let,
    Literal,
    Rec,
    Term,
    TypeAbstraction,
    TypeApplication,
    Var,
)

from aeon.utils.name import Name, fresh_counter


class ANFConverter:
    """Recursive visitor that applies ANF transformation."""

    def fresh(self) -> Name:
        return Name("anf", fresh_counter.fresh())

    def convert(self, t: Term):
        """Converts term to ANF form."""

        match t:
            case If(cond=cond, then=then, otherwise=otherwise, loc=loc):
                cond = self.convert(cond)
                then = self.convert(then)
                otherwise = self.convert(otherwise)
                if isinstance(cond, Var) or isinstance(cond, Literal):
                    return If(cond, then, otherwise, loc=loc)
                else:
                    v = self.fresh()
                    return self.convert(Let(v, cond, If(Var(v, cond.loc), then, otherwise, loc=loc), loc=cond.loc))
            case Application(fun=fun, arg=arg, loc=loc):
                fun = self.convert(fun)

                if isinstance(fun, Var) or isinstance(fun, Literal):
                    pass
                elif isinstance(fun, Let):
                    return Let(fun.var_name, fun.var_value, self.convert(Application(fun.body, arg, loc=loc)), loc=loc)
                else:
                    v = self.fresh()
                    return self.convert(Let(v, fun, Application(Var(v), arg, loc=loc), loc=loc))

                arg = self.convert(arg)
                if isinstance(arg, Var) or isinstance(arg, Literal):
                    return Application(fun, arg, loc=loc)
                else:
                    v = self.fresh()
                    return self.convert(Let(v, arg, Application(fun, Var(v), loc=loc), loc=loc))

            case Let(var_name=name, var_value=value, body=body, loc=loc):
                value = self.convert(value)
                body = self.convert(body)
                match value:
                    case Let(var_name=vname, var_value=vvalue, body=vbody, loc=iloc):
                        assert name != vname
                        vvalue = self.convert(vvalue)
                        vbody = self.convert(vbody)
                        return Let(vname, vvalue, self.convert(Let(name, vbody, body, loc=loc)), loc=iloc)
                    case Rec(var_name=vname, var_type=vtype, var_value=vvalue, body=vbody, loc=loc):
                        assert name != vname
                        vvalue = self.convert(vvalue)
                        vbody = self.convert(vbody)
                        return Rec(vname, vtype, vvalue, self.convert(Let(name, vbody, body, loc=loc)), loc=loc)
                    case _:
                        return Let(name, value, body, loc=loc)
            case Rec(var_name=name, var_type=type, var_value=value, body=body, loc=loc):
                value = self.convert(value)
                body = self.convert(body)
                return Rec(name, type, value, body, loc=loc)
            case Abstraction(var_name=name, body=body, loc=loc):
                body = self.convert(body)
                return Abstraction(var_name=name, body=body, loc=loc)
            case Annotation(expr=expr, type=ty, loc=loc):
                expr = self.convert(expr)
                return Annotation(expr=expr, type=ty, loc=loc)
            case TypeAbstraction(name=name, kind=kind, body=body, loc=loc):
                body = self.convert(body)
                return TypeAbstraction(name, kind, body, loc=loc)
            case TypeApplication(body=body, type=type, loc=loc):
                body = self.convert(body)
                return TypeApplication(body, type, loc=loc)
            case _:
                return t


def ensure_anf(t: Term) -> Term:
    """Converts a term to ANF form."""

    return ANFConverter().convert(t)
