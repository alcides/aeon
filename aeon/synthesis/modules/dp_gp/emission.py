"""Emit ordinary Aeon terms applying the generic pure DP combinators."""

from aeon.core.terms import Abstraction, Application, Literal, TypeApplication, Var
from aeon.core.types import AbstractionType, t_bool, t_int
from aeon.synthesis.modules.dp_gp.expressions import Expr, literal, variable
from aeon.utils.name import Name, fresh_counter


def apply(term, *args):
    for arg in args:
        term = Application(term, arg)
    return term


def integer(n):
    return Literal(n, t_int)


class Emitter:
    def __init__(self, names, vector_type):
        self.names = names
        self.vector_type = vector_type

    def call(self, name, *args):
        return apply(Var(self.names[name]), *args)

    def vector(self, args):
        result = Var(self.names["vnil"])
        for arg in reversed(tuple(args)):
            result = self.call("cell", arg, result)
        return result

    def get(self, vector, index):
        return self.call("get", vector, integer(index))

    def function(self, types, build, result_type):
        names = [Name(f"dp_arg{i}", fresh_counter.fresh()) for i, _ in enumerate(types)]
        body = build([Var(n) for n in names])
        ty = result_type
        for name, argument_type in reversed(list(zip(names, types))):
            body = Abstraction(name, body)
            ty = AbstractionType(name, argument_type, ty)
        return body, ty

    def relation(self, plan):
        def body(args):
            terms = []
            for i, mode in enumerate(plan.relation):
                if mode:
                    position = plan.solution_fields.index(i)
                    terms.append(
                        apply(
                            TypeApplication(Var(Name(("", "==", ">=", "<=")[mode], 0)), t_int),
                            self.get(args[0], position),
                            self.get(args[1], position),
                        )
                    )
            result = Literal(True, t_bool)
            for term in terms:
                result = apply(Var(Name("&&", 0)), result, term)
            return result

        return self.function([self.vector_type] * 2, body, t_bool)

    def projection(self, fields):
        return self.function(
            [self.vector_type], lambda args: self.vector(self.get(args[0], i) for i in fields), self.vector_type
        )

    def update(self, expression):
        return self.function([t_int, t_int], lambda args: expression.core(args), t_int)

    def algorithm(self, problem, plan, inputs):
        state_type = self.vector_type

        def state_values(s, action):
            return [
                self.get(s, plan.state_fields.index(i)) if i in plan.state_fields else integer(0) for i in range(3)
            ] + [action]

        allow, _ = self.function([state_type, t_int], lambda a: problem.allow.core(state_values(*a)), t_bool)
        step, _ = self.function(
            [state_type, t_int],
            lambda a: self.vector(problem.step[i].core(state_values(*a)) for i in plan.state_fields),
            state_type,
        )

        def build(args):
            s, action, p = args
            return self.vector(
                update.core([self.get(p, k), problem.delta[i].core(state_values(s, action))])
                for k, (i, update) in enumerate(zip(plan.solution_fields, plan.updates))
            )

        builder, _ = self.function([state_type, t_int, state_type], build, state_type)
        key, _ = self.function(
            [state_type],
            lambda a: self.vector(self.get(a[0], plan.state_fields.index(i)) for i in plan.key_fields),
            state_type,
        )
        score, _ = self.function(
            [state_type],
            lambda a: problem.score.core(
                [
                    self.get(a[0], plan.solution_fields.index(i)) if i in plan.solution_fields else integer(0)
                    for i in range(3)
                ]
            ),
            t_int,
        )
        dom, _ = self.relation(plan)
        return self.call(
            "solve",
            inputs[0],
            self.vector(problem.initial[i].core(inputs) for i in plan.state_fields),
            allow,
            step,
            builder,
            self.vector(integer(problem.base[i]) for i in plan.solution_fields),
            dom,
            key,
            score,
            integer(problem.floor),
        )


UPDATES = (
    variable(0),
    variable(1),
    literal(0),
    literal(1),
    Expr("+", (variable(0), variable(1))),
    Expr("-", (variable(0), variable(1))),
    Expr("*", (variable(0), variable(1))),
)
