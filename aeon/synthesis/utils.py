from aeon.ast import *
from aeon.types import TypingContext
from aeon.typechecker.zed import flatten_refined_types
from aeon.synthesis.ranges import RangedException, RangedContext

from aeon.libraries.stdlib import is_builtin

from multipledispatch import dispatch

# =============================================================================
# Filter the non-restricted refinements
@dispatch(TypingContext, Var)
def filter_refinements(ctx, condition):

    name = condition.name
    is_restricted = is_builtin(name) or name == RangedContext.Variable or\
                                        name in ctx.uninterpreted_functions

    return condition if is_restricted else None

@dispatch(TypingContext, Literal)
def filter_refinements(ctx, condition):
    return condition

@dispatch(TypingContext, If)
def filter_refinements(ctx, condition):
    
    cond = filter_refinements(ctx, condition.cond)
    then = filter_refinements(ctx, condition.then)
    otherwise = filter_refinements(ctx, condition.otherwise)

    # If any of the conditions was removed, then this is removed
    if not cond or not then or not otherwise:
        return None

    return condition

@dispatch(TypingContext, Abstraction)
def filter_refinements(ctx, condition):
    body = filter_refinements(ctx, condition.body)
    return condition if body else None

@dispatch(TypingContext, Application)
def filter_refinements(ctx, condition):
    
    # If it is the App(App(...))
    if isinstance(condition.target, Application):

        left = condition.target.target

        target = filter_refinements(ctx, condition.target)
        argument = filter_refinements(ctx, condition.argument)

        # If it is an expression like: -->, ||, &&, ==
        if (isinstance(left, Var) and left.name in ['-->', '||', '&&']) or\
        (isinstance(left, TApplication) and isinstance(left.target, Var) and left.target.name == '=='):
            
            # Both left and right are restricted refinements
            if target and argument:
                return condition
            # Only left is restricted
            if target and not argument:
                return condition.target.argument
            # Only right is restricted 
            elif not target and argument:
                return condition.argument
            
        if not argument or not target:
            return None

    # Anything else than the App(App(...))
    else:
        
        target = filter_refinements(ctx, condition.target)
        argument = filter_refinements(ctx, condition.argument)

        if not argument or not target:
            return None
        
    return condition

@dispatch(TypingContext, TAbstraction)
def filter_refinements(ctx, condition):
    body = filter_refinements(ctx, condition.body)
    return condition if body else None

@dispatch(TypingContext, TApplication)
def filter_refinements(ctx, condition):
    target = filter_refinements(ctx, condition.target)
    return condition if target else None

@dispatch(TypingContext, object)
def filter_refinements(ctx, condition):
    raise RangedException("Unknown node of type {} when filtering refinement: {}".format(type(condition), condition))


# =============================================================================
# Flattens the refinement
def flatten_refined_type(t):
    return flatten_refined_types(t)    