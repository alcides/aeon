from ..AeonASTVisitor import AeonASTVisitor
from ..generated.AeonParser import AeonParser
from ..generated.AeonVisitor import AeonVisitor

import sys
sys.path.append("..")
# from aeon3.stdlib import initial_context
from aeon3.ast import *
from aeon3.types import *
sys.path.remove("..")

class ContextVerifier(AeonVisitor):

    def __init__(self, errorList):
        self.errorList = errorList
        self.context = {'print', 'fix'} 
        self.aeonASTVisitor = AeonASTVisitor({})
        self.typeeContext = {t_v, t_o, t_f, t_i, t_b, t_s, bottom}

    def visitTypeeAlias(self, ctx:AeonParser.TypeeAliasContext):

        oldContext = self.context
        self.context = self.context.copy()

        self.visit(ctx.alias)

        typee = self.aeonASTVisitor.visit(ctx.name)
        alias = self.aeonASTVisitor.visit(ctx.alias)

        if typee in self.typeeContext:
            extraParam = (typee, alias)
            self.addError('TypeAlias', ctx.start.line, extraParam)

        self.typeeContext.add(typee)

        self.context = oldContext

    def visitTypeeDeclaration(self, ctx:AeonParser.TypeeDeclarationContext):
        
        oldContext = self.context
        self.context = self.context.copy()
        
        typee_error = self.visit(ctx.name)
        typee = self.aeonASTVisitor.visit(ctx)
        
        if typee in self.typeeContext:
            extraParam = (typee)
            self.addError('TypeDeclaration', ctx.start.line, extraParam)
        
        for arg in ctx.typee()[1:]:
            param_error = self.visit(arg)

        self.context = oldContext

        self.typeeContext.add(typee)

    def visitFunction(self, ctx:AeonParser.FunctionContext):
        
        if ctx.name.text in self.context:
            extraParam = (ctx.name.text)
            self.addError('Function', ctx.start.line, extraParam)

        self.context.add(ctx.name.text)
        
        oldContext = self.context
        self.context = self.context.copy()

        # Search for error in returnType
        self.visit(ctx.returnType)

        # Search for error in params if they exist
        if ctx.params:
            self.visit(ctx.params)

        # Compute the where function expression
        conditions = [self.visit(cond) for cond in ctx.expression()]

        if ctx.body():
            body = self.visit(ctx.body())

        self.context = oldContext

    def visitParameters(self, ctx:AeonParser.ParametersContext):
        self.visit(ctx.param)
        if ctx.restParams:
            self.visit(ctx.restParams)
    
    def visitTypeeBasicType(self, ctx:AeonParser.TypeeBasicTypeContext):
        self.context.add(ctx.varName.text)
        self.visit(ctx.typed)

    def visitTypeeAbstractionApplication(self, ctx:AeonParser.TypeeAbstractionApplicationContext):
        if len(ctx.name.text) > 1:
            if BasicType(ctx.name.text) not in self.typeeContext and \
                type(ctx.parentCtx) is not AeonParser.TypeeDeclarationContext:
                extraParam = (ctx.name.text)
                self.addError('Type', ctx.start.line, extraParam)
        if ctx.tabst:
            self.visit(ctx.tabst)

    def visitBodyVarDefinition(self, ctx:AeonParser.BodyVarDefinitionContext):
        self.visit(ctx.varType)
        self.visit(ctx.exp)
        if ctx.nextExpr:
            self.visit(ctx.nextExpr)

    def visitBodyAssignment(self, ctx:AeonParser.BodyAssignmentContext):
        if ctx.varName.text not in self.context:
            extraParam = (ctx.varName.text)
            self.addError('Variable', ctx.start.line, extraParam)

    def visitVariable(self, ctx:AeonParser.VariableContext):
        if ctx.varName.text not in self.context:
            extraParam = (ctx.varName.text)
            self.addError('Variable', ctx.start.line, extraParam)


    def visitFunctionCall(self, ctx:AeonParser.FunctionCallContext):
        if ctx.functionName.text not in self.context:
            extraParam = (ctx.functionName.text)
            self.addError('FunctionCall', ctx.start.line, extraParam)
        self.visitChildren(ctx)

    def addError(self, errorName, line, params):
        error = None
        if errorName == 'TypeAlias':
            error = '{}Error in line {}: The type {} in \'type {} as {}\' does not exist.'.format(\
                    errorName, line, params[1], params[0], params[1])
        elif errorName == 'TypeDeclaration':
            error = '{}Error in line {}: The type {} has already been declared.'.format(\
                    errorName, line, params)
        elif errorName == 'Function':
            error = '{}Error in line {}: The function {} has already been declared.'.format(\
                    errorName, line, params)
        elif errorName == 'Type':
            error = '{}Error in line {}: The basic type {} has not been declared.'.format(\
                    errorName, line, params)
        elif errorName == 'Variable':
            error = '{}Error in line {}: The variable {} has not been declared.'.format(\
                    errorName, line, params)
        elif errorName == 'FunctionCall':
            error = '{}Error in line {}: The function {} has not been declared'.format(\
                    errorName, line, params)

        print(error)
        self.errorList.append(error)