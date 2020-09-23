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
