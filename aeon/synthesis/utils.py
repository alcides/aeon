from aeon.ast import *
from aeon.types import TypingContext, BasicType
from aeon.typechecker.type_simplifier import reduce_type
#from aeon.synthesis.ranges import RangedException, RangedContext

from aeon.libraries.stdlib import is_builtin

from multipledispatch import dispatch


# =============================================================================
# Filter the non-restricted refinements
@dispatch(TypingContext, str, Var)
def filter_refinements(ctx, name, condition):

    var = condition.name
    is_restricted = is_builtin(var) or var == name or \
                                        var in ctx.uninterpreted_functions or \
                                        isinstance(ctx.variables[var], BasicType)

    return condition if is_restricted else None


@dispatch(TypingContext, str, Literal)
def filter_refinements(ctx, name, condition):
    return condition


@dispatch(TypingContext, str, If)
def filter_refinements(ctx, name, condition):

    cond = filter_refinements(ctx, name, condition.cond)
    then = filter_refinements(ctx, name, condition.then)
    otherwise = filter_refinements(ctx, name, condition.otherwise)

    # If any of the conditions was removed, then this is removed
    if not cond or not then or not otherwise:
        return None

    return condition


@dispatch(TypingContext, str, Abstraction)
def filter_refinements(ctx, name, condition):
    body = filter_refinements(ctx, name, condition.body)
    return condition if body else None


@dispatch(TypingContext, str, Application)
def filter_refinements(ctx, name, condition):

    # If it is the App(App(...))
    if isinstance(condition.target, Application):

        left = condition.target.target

        target = filter_refinements(ctx, name, condition.target)
        argument = filter_refinements(ctx, name, condition.argument)

        # If it is an expression like: -->, ||, &&, ==
        if (isinstance(left, Var) and left.name in ['-->', '||', '&&']):

            # Both left and right are restricted refinements
            if target and argument:
                return condition
            # Only left is restricted
            if target and not argument:
                return condition.target.argument
            # Only right is restricted
            elif not target and argument:
                return condition.argument

    # Anything else than the App(App(...))
    else:
        target = filter_refinements(ctx, name, condition.target)
        argument = filter_refinements(ctx, name, condition.argument)

    return condition if target and argument else None


@dispatch(TypingContext, str, TAbstraction)
def filter_refinements(ctx, name, condition):
    body = filter_refinements(ctx, name, condition.body)
    return condition if body else None


@dispatch(TypingContext, str, TApplication)
def filter_refinements(ctx, name, condition):
    target = filter_refinements(ctx, name, condition.target)
    return condition if target else None


@dispatch(TypingContext, str, object)
def filter_refinements(ctx, name, condition):
    raise RangedException(
        "Unknown node of type {} when filtering refinement: {}".format(
            type(condition), condition))


# =============================================================================
# Flattens the refinement
def flatten_refined_type(t):
    return reduce_type(None, t)


# =============================================================================
def substitute_uninterpreted(node, uninterp, replacement):

    assert (isinstance(node, TypedNode))
    assert (isinstance(uninterp, str))
    assert (isinstance(uninterp, str))

    subs = lambda x: substitute_uninterpreted(x, uninterp, replacement)

    if isinstance(node, Literal):
        return node

    elif isinstance(node, Var):
        return None if node.name == uninterp else node

    elif isinstance(node, Application):
        target = subs(node.target)
        argument = subs(node.argument)

        if target == None or argument == None:
            return Var(replacement)

        return Application(target, argument)

    elif isinstance(node, Abstraction):
        name = node.arg_name
        T = node.arg_type

        if isinstance(T, RefinedType):
            T.cond = subs(T.cond)

        body = subs(node.body)

        if body == None:
            return None

        return Abstraction(name, T, body)

    elif isinstance(node, TApplication):
        return subs(node.target)

    elif isinstance(node, TAbstraction):
        return subs(node.body)

    else:
        raise TypeException("Substitution in uninterp unknown:", node,
                            type(node))
