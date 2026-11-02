"""Total, pure scalar expressions shared by the DP checker and Aeon emitter."""

from dataclasses import dataclass
import operator

import z3

from aeon.core.terms import Abstraction, Annotation, Application, If, Let, Literal, TypeApplication, Var
from aeon.core.types import t_bool, t_int
from aeon.synthesis.api import UnsupportedSynthesisGoal
from aeon.utils.name import Name


OPS = {
    "+": operator.add,
    "-": operator.sub,
    "*": operator.mul,
    "==": operator.eq,
    "!=": operator.ne,
    "<": operator.lt,
    "<=": operator.le,
    ">": operator.gt,
    ">=": operator.ge,
    "&&": lambda a, b: a and b,
    "||": lambda a, b: a or b,
    "!": operator.not_,
}


@dataclass(frozen=True)
class Expr:
    op: str
    args: tuple = ()

    def boolean(self):
        if self.op == "lit":
            return type(self.args[0]) is bool
        if self.op == "if":
            return self.args[1].boolean()
        return self.op in ("==", "!=", "<", "<=", ">", ">=", "&&", "||", "!")

    def run(self, values):
        if self.op == "var":
            return values[self.args[0]]
        if self.op == "lit":
            return self.args[0]
        if self.op == "if":
            return self.args[1 if self.args[0].run(values) else 2].run(values)
        return OPS[self.op](*(a.run(values) for a in self.args))

    def symbolic(self, values):
        if self.op == "var":
            return values[self.args[0]]
        if self.op == "lit":
            return z3.BoolVal(self.args[0]) if type(self.args[0]) is bool else z3.IntVal(self.args[0])
        children = [a.symbolic(values) for a in self.args]
        special = {"if": z3.If, "&&": z3.And, "||": z3.Or, "!": z3.Not}
        return special.get(self.op, OPS.get(self.op))(*children)

    def core(self, variables):
        if self.op == "var":
            return variables[self.args[0]]
        if self.op == "lit":
            value = self.args[0]
            return Literal(value, t_bool if type(value) is bool else t_int)
        children = [a.core(variables) for a in self.args]
        if self.op == "if":
            return If(*children)
        term = Var(Name(self.op, 0))
        if self.op not in ("&&", "||", "!"):
            term = TypeApplication(term, t_bool if self.args[0].boolean() else t_int)
        for child in children:
            term = Application(term, child)
        return term

    def variables(self):
        if self.op == "var":
            return {self.args[0]}
        if self.op == "lit":
            return set()
        return set().union(*(a.variables() for a in self.args))

    def replace(self, mapping):
        if self.op == "var":
            return mapping.get(self.args[0], self)
        if self.op == "lit":
            return self
        return Expr(self.op, tuple(a.replace(mapping) for a in self.args))


def variable(index):
    return Expr("var", (index,))


def literal(value):
    return Expr("lit", (value,))


def applications(term):
    args = []
    while isinstance(term, (Application, TypeApplication, Annotation)):
        if isinstance(term, Application):
            args.append(term.arg)
            term = term.fun
        else:
            term = term.body if isinstance(term, TypeApplication) else term.expr
    return term, tuple(reversed(args))


def extract(term, definitions, bindings=None, expanding=frozenset(), work=None):
    """Inline only acyclic scalar helpers; no native calls, effects or recursion."""
    bindings = {} if bindings is None else bindings
    work = [5000] if work is None else work
    work[0] -= 1
    if work[0] < 0 or len(expanding) > 32:
        raise UnsupportedSynthesisGoal("dp_gp scalar reference exceeds expansion limits")

    def visit(child, env=bindings, active=expanding):
        return extract(child, definitions, env, active, work)

    if isinstance(term, Literal) and type(term.value) in (int, bool):
        return literal(term.value)
    if isinstance(term, Var) and term.name in bindings:
        return bindings[term.name]
    if isinstance(term, Annotation):
        return visit(term.expr)
    if isinstance(term, If):
        return Expr("if", (visit(term.cond), visit(term.then), visit(term.otherwise)))
    if isinstance(term, Let):
        return visit(term.body, {**bindings, term.var_name: visit(term.var_value)})
    head, args = applications(term)
    if isinstance(head, Var) and head.name.id == 0 and head.name.name in OPS:
        expected = 1 if head.name.name == "!" else 2
        if len(args) == expected:
            return Expr(head.name.name, tuple(visit(a) for a in args))
    if isinstance(head, Var) and head.name in definitions and head.name not in expanding:
        body = definitions[head.name]
        env = dict(bindings)
        for arg in args:
            if not isinstance(body, Abstraction):
                break
            env[body.var_name] = visit(arg)
            body = body.body
        else:
            return visit(body, env, expanding | {head.name})
    raise UnsupportedSynthesisGoal("dp_gp requires total scalar reference expressions (+, -, *, comparisons, if)")


def function(term, arity, definitions):
    head, args = applications(term)
    if args or not isinstance(head, Var) or head.name not in definitions:
        raise UnsupportedSynthesisGoal("dp_gp expects named scalar component functions")
    body = definitions[head.name]
    bindings = {}
    for index in range(arity):
        if not isinstance(body, Abstraction):
            raise UnsupportedSynthesisGoal("dp_gp reference component has the wrong arity")
        bindings[body.var_name] = variable(index)
        body = body.body
    return extract(body, definitions, bindings, frozenset({head.name}))
