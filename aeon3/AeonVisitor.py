# Generated from Aeon.g4 by ANTLR 4.7.2
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .AeonParser import AeonParser
else:
    from AeonParser import AeonParser

# This class defines a complete generic visitor for a parse tree produced by AeonParser.

class AeonVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by AeonParser#aeon.
    def visitAeon(self, ctx:AeonParser.AeonContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#RegularImport.
    def visitRegularImport(self, ctx:AeonParser.RegularImportContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#SpecialImport.
    def visitSpecialImport(self, ctx:AeonParser.SpecialImportContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#importName.
    def visitImportName(self, ctx:AeonParser.ImportNameContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#typeeAlias.
    def visitTypeeAlias(self, ctx:AeonParser.TypeeAliasContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#typeeDeclaration.
    def visitTypeeDeclaration(self, ctx:AeonParser.TypeeDeclarationContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#attribute.
    def visitAttribute(self, ctx:AeonParser.AttributeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#function.
    def visitFunction(self, ctx:AeonParser.FunctionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#SingleParameter.
    def visitSingleParameter(self, ctx:AeonParser.SingleParameterContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#MultipleParameters.
    def visitMultipleParameters(self, ctx:AeonParser.MultipleParametersContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#TypeeBasicType.
    def visitTypeeBasicType(self, ctx:AeonParser.TypeeBasicTypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#TypeeAbstraction.
    def visitTypeeAbstraction(self, ctx:AeonParser.TypeeAbstractionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#TypeeCondition.
    def visitTypeeCondition(self, ctx:AeonParser.TypeeConditionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#TypeeParenthesis.
    def visitTypeeParenthesis(self, ctx:AeonParser.TypeeParenthesisContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#BodyVarDefinition.
    def visitBodyVarDefinition(self, ctx:AeonParser.BodyVarDefinitionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#BodyAssignment.
    def visitBodyAssignment(self, ctx:AeonParser.BodyAssignmentContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#IfThenElse.
    def visitIfThenElse(self, ctx:AeonParser.IfThenElseContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#BodyExpression.
    def visitBodyExpression(self, ctx:AeonParser.BodyExpressionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#Parenthesis.
    def visitParenthesis(self, ctx:AeonParser.ParenthesisContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#Variable.
    def visitVariable(self, ctx:AeonParser.VariableContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#BinaryOperationCall.
    def visitBinaryOperationCall(self, ctx:AeonParser.BinaryOperationCallContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#Literal.
    def visitLiteral(self, ctx:AeonParser.LiteralContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#UnaryOperationCall.
    def visitUnaryOperationCall(self, ctx:AeonParser.UnaryOperationCallContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#FunctionCall.
    def visitFunctionCall(self, ctx:AeonParser.FunctionCallContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#Abstraction.
    def visitAbstraction(self, ctx:AeonParser.AbstractionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#IfThenElseExpr.
    def visitIfThenElseExpr(self, ctx:AeonParser.IfThenElseExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#dottedName.
    def visitDottedName(self, ctx:AeonParser.DottedNameContext):
        return self.visitChildren(ctx)



del AeonParser