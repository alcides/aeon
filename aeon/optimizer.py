from aeon.ast import Literal, Var, If, Application, Abstraction, TApplication, TAbstraction
from aeon.types import BasicType, RefinedType, AbstractionType, TypeApplication, TypeAbstraction, t_i, t_f, t_b, t_s, top

from aeon.interpreter import run, EvaluationException

from multipledispatch import dispatch


class OptimizeLiteralException(Exception):
    pass


global op
op = ['+', '-', '*', '/', '%', '>', '<', '>=', '<=', \
      '!', '||', '&&', '-->', '==', '!=']

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

zero = Literal(0, t_i)
one = Literal(1, t_i)

# Sum rules
rule1 = lambda left, right: (left, None) if right == zero else ((None, right) if left == zero else (left, right))

# Minus rules
rule2 = lambda left, right: (left, None) if right == zero else (left, right)

# Mult rules
rule3 = lambda left, right: (None, right) if right == zero else ((left, None) if left == zero else (left, right))
rule4 = lambda left, right: (left, None) if right == one else ((None, right) if left == one else (left, right))

# Mod & Division rules
rule5 = lambda left, right: (left, None) if left == zero else (left, right)

rules = {
    '+' : [rule1],
    '-' : [rule2],
    '*' : [rule3, rule4], 
    '/' : [rule5],
}

def apply_rules(operation, target, argument):

    op_rules = rules.get(operation)

    if isinstance(target, Application):
        left = target.argument
    else:
        left = target

    right = argument

    if operation and op_rules:
        for rule in op_rules:
            left, right = rule(left, right)

            if left is None:
                return right   

            elif right is None:
                return left

    return Application(target, argument)


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

    # Optimize each one of the subtrees
    cond = optimize(iff.cond)
    then = optimize(iff.then)
    otherwise = optimize(iff.otherwise)

    try:
        evaluated_cond = run(iff.cond)
        result = then if evaluated_cond else otherwise

    # This ensures there is a non-native variable in the condition
    except EvaluationException:
        # If both then and otherwise are the same, this If is useless
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
        # This ensures that there is a non-native variable in context
        except EvaluationException:
            result = apply_rules(get_op(app), target, argument)
        # This means that the current application is a lambda function
        except OptimizeLiteralException:
            result = app

    return result

@dispatch(Abstraction)
def optimize(abst):
    
    abst.body = optimize(abst.body)

    # If the variable is not used in the body, then the abstraction is useless
    if not exists_var(abst.arg_name, abst.body):
        return optimize(abst.body)

    return abst

@dispatch(TApplication)
def optimize(tapp):
    tapp.target = optimize(tapp.target)
    return tapp 
    
@dispatch(TAbstraction)
def optimize(tabs):
    tabs.body = optimization(tabs.body) 
    return tabs

@dispatch(object)
def optimize(none):
    raise Exception("Unknown node type during optimization: ", type(node))