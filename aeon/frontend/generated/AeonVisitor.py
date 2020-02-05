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


    # Visit a parse tree produced by AeonParser#imprt.
    def visitImprt(self, ctx:AeonParser.ImprtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#regular_import.
    def visitRegular_import(self, ctx:AeonParser.Regular_importContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#function_import.
    def visitFunction_import(self, ctx:AeonParser.Function_importContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#import_path.
    def visitImport_path(self, ctx:AeonParser.Import_pathContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#typee_alias.
    def visitTypee_alias(self, ctx:AeonParser.Typee_aliasContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#typee_declaration.
    def visitTypee_declaration(self, ctx:AeonParser.Typee_declarationContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#regular_typee_declaration.
    def visitRegular_typee_declaration(self, ctx:AeonParser.Regular_typee_declarationContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#parameterized_typee_declaration.
    def visitParameterized_typee_declaration(self, ctx:AeonParser.Parameterized_typee_declarationContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#parameters_typee_declaration.
    def visitParameters_typee_declaration(self, ctx:AeonParser.Parameters_typee_declarationContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#typee.
    def visitTypee(self, ctx:AeonParser.TypeeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#typee_refined.
    def visitTypee_refined(self, ctx:AeonParser.Typee_refinedContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#typee_abstraction_type.
    def visitTypee_abstraction_type(self, ctx:AeonParser.Typee_abstraction_typeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#typee_definition.
    def visitTypee_definition(self, ctx:AeonParser.Typee_definitionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#typee_basic_type.
    def visitTypee_basic_type(self, ctx:AeonParser.Typee_basic_typeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#typee_type_abstract.
    def visitTypee_type_abstract(self, ctx:AeonParser.Typee_type_abstractContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#typee_abstract_parameters.
    def visitTypee_abstract_parameters(self, ctx:AeonParser.Typee_abstract_parametersContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#function.
    def visitFunction(self, ctx:AeonParser.FunctionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#function_identifier.
    def visitFunction_identifier(self, ctx:AeonParser.Function_identifierContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#function_parameters.
    def visitFunction_parameters(self, ctx:AeonParser.Function_parametersContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#function_where.
    def visitFunction_where(self, ctx:AeonParser.Function_whereContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#NativeBody.
    def visitNativeBody(self, ctx:AeonParser.NativeBodyContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#UninterpretedBody.
    def visitUninterpretedBody(self, ctx:AeonParser.UninterpretedBodyContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#RegularBody.
    def visitRegularBody(self, ctx:AeonParser.RegularBodyContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#statement.
    def visitStatement(self, ctx:AeonParser.StatementContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#variable_definition.
    def visitVariable_definition(self, ctx:AeonParser.Variable_definitionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#variable_assignment.
    def visitVariable_assignment(self, ctx:AeonParser.Variable_assignmentContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#if_statement.
    def visitIf_statement(self, ctx:AeonParser.If_statementContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#FitnessImprovement.
    def visitFitnessImprovement(self, ctx:AeonParser.FitnessImprovementContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#LogicalExpression.
    def visitLogicalExpression(self, ctx:AeonParser.LogicalExpressionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#IfExpression.
    def visitIfExpression(self, ctx:AeonParser.IfExpressionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#Parenthesis.
    def visitParenthesis(self, ctx:AeonParser.ParenthesisContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#Hole.
    def visitHole(self, ctx:AeonParser.HoleContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#UnaryOperation.
    def visitUnaryOperation(self, ctx:AeonParser.UnaryOperationContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#Variable.
    def visitVariable(self, ctx:AeonParser.VariableContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#AbstractionExpression.
    def visitAbstractionExpression(self, ctx:AeonParser.AbstractionExpressionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#Literal.
    def visitLiteral(self, ctx:AeonParser.LiteralContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#NumberExpression.
    def visitNumberExpression(self, ctx:AeonParser.NumberExpressionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#FunctionCall.
    def visitFunctionCall(self, ctx:AeonParser.FunctionCallContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#TypeeAttributeCall.
    def visitTypeeAttributeCall(self, ctx:AeonParser.TypeeAttributeCallContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#function_abstraction.
    def visitFunction_abstraction(self, ctx:AeonParser.Function_abstractionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#call_parameters.
    def visitCall_parameters(self, ctx:AeonParser.Call_parametersContext):
        return self.visitChildren(ctx)



del AeonParser