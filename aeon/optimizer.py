from aeon.ast import Literal, Var, If, Application, Abstraction, TApplication, TAbstraction
from aeon.types import BasicType, RefinedType, AbstractionType, TypeApplication, TypeAbstraction, t_i, t_f, t_b, t_s, top

from aeon.interpreter import run, EvaluationException

from multipledispatch import dispatch


class OptimizeLiteralException(Exception):
    pass


global op
op = ['+', '-', '*', '/', '%', '>', '<', '>=', '<=', '!', '||', '&&', '-->']

def is_un_op(node):
    return isinstance(node, Application) and isinstance(node.target, Var) and \
           node.target.name in op

def is_bin_op_reg(node):
    return isinstance(node, Application) and \
           isinstance(node.target, Application) and \
           isinstance(node.target.target, TApplication) and \
           isinstance(node.target.target.target, Var) and \
           node.target.target.target.name in op

def is_bin_op_bool(node):
    return isinstance(node, Application) and \
           isinstance(node.target, Application) and \
           isinstance(node.target.target, Var) and \
           node.target.target.name in op

def is_bin_op(node):
    return is_bin_op_reg(node) or is_bin_op_bool(node)

def get_op(node):
    if is_un_op(node):
        return node.target.name
    elif is_bin_op_reg(node):
        return node.target.target.target.name
    elif is_bin_op_bool(node):
        return node.target.target.name in op
    else:
        return None

# =============================================================================
# Special arithmetic rules: (0 / x) = 0, (0 * x) = 0, (0 * (x + 1)) = (x + 1)
global rules
rules = {
    '+' : [lambda left, right: left if right == 0 else (right if left == 0 else (left, right))],
    '-' : [lambda left, right: None]
}

def check_rule(operation, left, right):
    pass


# =============================================================================
def mk_literal(value):
    if isinstance(value, int):
        return Literal(value, t_i)
    elif isinstance(value, float):
        return Literal(value, t_f)
    elif isinstance(value, bool):
        return Literal(value, t_b)
    elif isinstance(value, str):
        return Literal(value, t_s)
    raise OptimizeLiteralException("Unallowed value in make literal:", type(value))

def exists_var(name, node):

    if isinstance(node, Literal):
        return False

    elif isinstance(node, Var):
        return node.name == name
    
    elif isinstance(node, If):
        return exists_var(name, node.cond) or exists_var(name, node.then) or \
               exists_var(name, node.otherwise)

    elif isinstance(node, Application):
        return exists_var(name, node.target) or exists_var(name, node.argument)
    
    elif isinstance(node, Abstraction):
        return (node.arg_name == name) or exists_var(name, node.body)

    elif isinstance(node, TAbstraction):
        return exists_var(name, node.body)
    
    elif isinstance(node, TApplication):
        return exists_var(name, node.target)
    
    return False

# =============================================================================
# Responsible for the optimization of code (removal of spurious code)
@dispatch(Literal)
def optimize(literal):
    return literal

@dispatch(Var)
def optimize(var):
    return var

@dispatch(If)
def optimize(iff):

    cond = optimize(iff.cond)
    then = optimize(iff.then)
    otherwise = optimize(iff.otherwise)

    try:
        evaluated_cond = run(iff.cond)

        if evaluated_cond:
            result = then
        else:
            result = otherwise

    except EvaluationException:
    
        if then == otherwise:
            result = then
        else:
            iff.cond = cond
            iff.then = then
            iff.otherwise = otherwise

            result = iff 

    return result

@dispatch(Application)
def optimize(app):
    
    target = optimize(app.target)
    argument = optimize(app.argument)
    
    # It tells us that the abstraction did not use the variable in the body
    if isinstance(app.target, Abstraction) and \
       not isinstance(target, Abstraction):
        return target

    else:
        try:
            result = mk_literal(run(app))
        except EvaluationException:
            result = Application(target, argument)
        except OptimizeLiteralException:
            result = app

    return result

@dispatch(Abstraction)
def optimize(abst):
    if not exists_var(abst.arg_name, abst.body):
        return optimize(abst.body)
    
    abst.body = optimize(abst.body)

    return abst

@dispatch(TApplication)
def optimize(tapp):
    target = optimize(tapp.target)
    return TApplication(target, tapp.argument)

@dispatch(TAbstraction)
def optimize(tabs):
    pass

@dispatch(object)
def optimize(none):
    raise Exception("Unknown node type during optimization: ", type(node))