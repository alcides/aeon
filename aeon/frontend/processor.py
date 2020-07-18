from multipledispatch import dispatch

from aeon.ast import *
from aeon.types import *

from aeon.frontend.utils import generate_uninterpreted

from typing import Dict

'''
This processor is responsible for completing the aeon ast with information
that we couldn't produce during the frontend due to lark bottom up approach.
This processor is responsible for the following procedures:
    * Assign the type to assign statements
    * Convert uninterpreted invocations to function invocations: x.y -> T_y(x)
'''
class ProcessContext(object):
    def __init__(self):
        self.vars = dict()
        self.tdecls = dict()
        self.taliases = dict()
    
    def copy(self):
        pctx = ProcessContext()
        pctx.vars : Dict[str, Type] = self.vars.copy()
        pctx.tdecls : Dict[str, Kind] = self.tdecls.copy()
        pctx.taliases : Dict[str, Type] = self.taliases.copy()
        return pctx


# =============================================================================

def process_aeon(declarations):
    context = ProcessContext()
    return [process(context, decl) for decl in declarations]

# =============================================================================
# Statements
@dispatch(ProcessContext, Import)
def process(ctx : ProcessContext, iimport):
    return iimport

@dispatch(ProcessContext, TypeDeclaration)
def process(ctx : ProcessContext, typedecl):
    ctx.tdecls[typedecl.name] = typedecl.kind
    return typedecl

@dispatch(ProcessContext, TypeAlias)
def process(ctx : ProcessContext, typealias):
    typealias.type = process(ctx, typealias.type)
    ctx.taliases[typealias.name] = typealias.type
    return typealias

@dispatch(ProcessContext, Definition)
def process(ctx : ProcessContext, definition):
    definition.type = process(ctx, definition.type)
    definition.return_type = process(ctx, definition.return_type)

    ctx.vars[definition.name] = definition.type

    definition.body = process(ctx.copy(), definition.body)

    return definition

# =============================================================================
# Nodes
@dispatch(ProcessContext, Hole)
def process(ctx : ProcessContext, hole):
    hole.type = process(ctx, hole.type)
    return hole

@dispatch(ProcessContext, Literal)
def process(ctx : ProcessContext, literal):
    return literal

@dispatch(ProcessContext, Var)
def process(ctx : ProcessContext, var):
    if '.' in var.name:
        return generate_uninterpreted(ctx, var.name)
    return var

@dispatch(ProcessContext, If)
def process(ctx : ProcessContext, iff):
    iff.cond = process(ctx, iff.cond)
    iff.then = process(ctx.copy(), iff.then)
    iff.otherwise = process(ctx.copy(), iff.otherwise)
    return iff

@dispatch(ProcessContext, Application)
def process(ctx : ProcessContext, app):
    app.target = process(ctx, app.target)
    app.argument = process(ctx, app.argument)
    return app

@dispatch(ProcessContext, Abstraction)
def process(ctx : ProcessContext, abst):
    ctx = ctx.copy()

    if abst.arg_type == None:
        abst.arg_type = ctx.vars[abst.arg_name]
    
    # Process the arg_type
    abst.arg_type = process(ctx, abst.arg_type)
    # Append the variable with the type to the context
    ctx.vars[abst.arg_name] = abst.arg_type    
    # Process the body
    abst.body = process(ctx, abst.body)

    return abst

@dispatch(ProcessContext, TApplication)
def process(ctx : ProcessContext, tapp):
    tapp.target = process(ctx, tapp.target)
    tapp.argument = process(ctx, tapp.argument)
    return tapp 

@dispatch(ProcessContext, TAbstraction)
def process(ctx : ProcessContext, tabs):
    ctx = ctx.copy()
    ctx.tdecls[tabs.typevar] = tabs.kind
    tabs.body = process(ctx, tabs.body)
    return tabs

# =============================================================================
# Types
@dispatch(ProcessContext, BasicType)
def process(ctx : ProcessContext, typee):
    if typee.name in ctx.taliases:
        return ctx.taliases[typee.name]
    return typee

@dispatch(ProcessContext, RefinedType)
def process(ctx : ProcessContext, typee):
    ctx = ctx.copy()
    # Process the type type
    typee.type = process(ctx, typee.type)
    ctx.vars[typee.name] = typee.type
    # Process the type condition
    typee.cond = process(ctx, typee.cond)
    return typee

@dispatch(ProcessContext, AbstractionType)
def process(ctx, typee):
    ctx = ctx.copy()
    # Process the type arg_type
    typee.arg_type = process(ctx, typee.arg_type)
    ctx.vars[typee.arg_name] = typee.arg_type
    # Process the type return type
    typee.return_type = process(ctx, typee.return_type)
    return typee
    

@dispatch(ProcessContext, TypeApplication)
def process(ctx, typee):
    typee.target = process(ctx, typee.target)
    typee.argument = process(ctx, typee.argument)
    return typee 

@dispatch(ProcessContext, TypeAbstraction)
def process(ctx, typee):
    ctx = ctx.copy()
    ctx.tdecls[typee.name] = typee.kind
    typee.type = process(ctx, typee.type)
    return typee