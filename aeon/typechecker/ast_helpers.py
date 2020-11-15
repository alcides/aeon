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



smt_true = Literal(True, t_b)
smt_and = lambda x, y: x == smt_true and y or (
    y == smt_true and x or Application(Application(Var("smtAnd"), x), y))
smt_eq = lambda x, y: Application(Application(Var("smtEq"), x), y)

smt_not = lambda x: Application(Var("smtNot"), x)
