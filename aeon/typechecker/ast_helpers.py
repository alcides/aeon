from typing import Tuple
from aeon.types import *
from aeon.ast import *


def make_equality_int(name:str, v:int):
    return Application(Application(Var("smtEq"), Var(name)), Literal(value=v, type=t_i, ensured=True))

def make_equality_bool(name:str, v:bool):
    return Application(Application(Var("smtEq"), Var(name)), Literal(value=v, type=t_b, ensured=True))

def make_equality_str(name:str, v:str):
    return Application(Application(Var("smtEq"), Var(name)), Literal(value=v, type=t_s, ensured=True))

def make_equality_float(name:str, v:float):
    return Application(Application(Var("smtEq"), Var(name)), Literal(value=v, type=t_f, ensured=True))

def make_equality_vars(name:str, name2:str):
    return Application(Application(Var("smtEq"), Var(name)), Var(name2))



def is_unop(a: TypedNode, name: str = "") -> bool:
    return isinstance(a, Application) and isinstance(
        a.target, Var) and (name != "" and a.target.name == name)


def mk_unop(t: str, a: TypedNode):
    return Application(Var(t), a)


def is_binop(a: TypedNode, name: str = "") -> bool:
    return isinstance(
        a, Application) and isinstance(a.target, Application) and isinstance(
            a.target.target, Var) and (name != ""
                                       and a.target.target.name == name)


def binop_args(a: TypedNode) -> Tuple[TypedNode, TypedNode]:
    assert (isinstance(a, Application) and isinstance(a.target, Application))
    return (a.target.argument, a.argument)


def mk_binop(t: str, a: TypedNode, b: TypedNode):
    return Application(Application(Var(t), a), b)


def is_t_binop(a: TypedNode, name: str = "") -> bool:
    return isinstance(
        a, Application) and isinstance(a.target, Application) and isinstance(
            a.target.target, TApplication) and isinstance(
                a.target.target.target,
                Var) and (name != "" and a.target.target.target.name == name)


def t_binop_args(a: TypedNode) -> Tuple[TypedNode, TypedNode, Type]:
    assert (isinstance(a, Application) and isinstance(a.target, Application)
            and isinstance(a.target.target, TApplication)
            and isinstance(a.target.target.target, Var))
    return (a.target.argument, a.argument, a.target.target.argument)


def mk_t_binop(name: str, t: Type, a: TypedNode, b: TypedNode):
    return Application(Application(TApplication(Var(name), t), a), b)



smt_true = Literal(True, t_b)
smt_false = Literal(False, t_b)
smt_and = lambda x, y: x == smt_true and y or (
    y == smt_true and x or mk_binop("smtAnd", x, y))
smt_or = lambda x, y: x == smt_true and smt_true or (
    y == smt_true and smt_true or mk_binop("smtOr", x, y))

smt_eq = lambda x, y: mk_binop("smtEq", x, y)

smt_not = lambda x: x == smt_true and smt_false or (x == smt_true and smt_false or mk_unop("smtNot", x))


