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

from aeon.utils.name import Name


class ANFConverter:
    """Recursive visitor that applies ANF transformation."""

    def __init__(self, starting_counter: int = 0):
        self.counter = starting_counter

    def fresh(self) -> Name:
        self.counter += 1
        return Name("anf", self.counter)

    def convert(self, t: Term):
        """Converts term to ANF form."""

        match t:
            case If(cond=cond, then=then, otherwise=otherwise):
                cond = self.convert(cond)
                then = self.convert(then)
                otherwise = self.convert(otherwise)
                if isinstance(cond, Var) or isinstance(cond, Literal):
                    return If(cond, then, otherwise)
                else:
                    v = self.fresh()
                    return self.convert(Let(v, cond, If(Var(v), then, otherwise)))
            case Application(fun=fun, arg=arg):
                fun = self.convert(fun)

                if isinstance(fun, Var) or isinstance(fun, Literal):
                    pass
                elif isinstance(fun, Let):
                    return Let(
                        fun.var_name,
                        fun.var_value,
                        self.convert(Application(fun.body, arg)),
                    )
                else:
                    v = self.fresh()
                    return self.convert(Let(v, fun, Application(Var(v), arg)))

                arg = self.convert(arg)
                if isinstance(arg, Var) or isinstance(arg, Literal):
                    return Application(fun, arg)
                else:
                    v = self.fresh()
                    return self.convert(Let(v, arg, Application(fun, Var(v))))

            case Let(var_name=name, var_value=value, body=body):
                value = self.convert(value)
                body = self.convert(body)
                match value:
                    case Let(var_name=vname, var_value=vvalue, body=vbody):
                        assert name != vname
                        vvalue = self.convert(vvalue)
                        vbody = self.convert(vbody)
                        return Let(
                            vname,
                            vvalue,
                            self.convert(Let(name, vbody, body)),
                        )
                    case Rec(var_name=vname, var_type=vtype, var_value=vvalue, body=vbody):
                        assert name != vname
                        vvalue = self.convert(vvalue)
                        vbody = self.convert(vbody)
                        return Rec(
                            vname,
                            vtype,
                            vvalue,
                            self.convert(Let(name, vbody, body)),
                        )
                    case _:
                        return Let(name, value, body)
            case Rec(var_name=name, var_type=type, var_value=value, body=body):
                value = self.convert(value)
                body = self.convert(body)
                return Rec(name, type, value, body)
            case Abstraction(var_name=name, body=body):
                body = self.convert(body)
                return Abstraction(var_name=name, body=body)
            case Annotation(expr=expr, type=ty):
                expr = self.convert(expr)
                return Annotation(expr=expr, type=ty)
            case TypeAbstraction(name=name, kind=kind, body=body):
                body = self.convert(body)
                return TypeAbstraction(name, kind, body)
            case TypeApplication(body=body, type=type):
                body = self.convert(body)
                return TypeApplication(body, type)
            case _:
                return t


def ensure_anf(t: Term, starting_counter: int = 0) -> Term:
    """Converts a term to ANF form."""

    return ANFConverter(starting_counter=starting_counter).convert(t)
