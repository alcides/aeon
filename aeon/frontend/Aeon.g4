/**
 * Grammar for the Aeon language
 * To compile the grammar: java -jar ../../lib/antlr-4.7.2-complete.jar -Dlanguage=Python3 -visitor -no-listener -o generated Aeon.g4
 */
grammar Aeon;

aeon
    : (imprt | typee_alias | typee_declaration | function | statement | typee)* EOF ;

// ----------------------------------------------------------------------------
// ---------------------------------- Import ----------------------------------
imprt
    : regular_import
    | function_import
    ;

regular_import
    : IMPORT path=import_path SEMICOLON
    ;

function_import
    : IMPORT functionName=IDENTIFIER FROM path=import_path SEMICOLON
    ;

import_path
    : (directory=(DOTDOT | IDENTIFIER) QUOT)* name=IDENTIFIER
    ;

// ----------------------------------------------------------------------------
// -------------------------------- TypeeAlias --------------------------------
typee_alias
    : TYPEE name=typee_basic_type AS alias=typee SEMICOLON
    ;

// ----------------------------------------------------------------------------
// ----------------------------- TypeeDeclaration -----------------------------
typee_declaration
    : regular_typee_declaration
    | parameterized_typee_declaration
    ;

regular_typee_declaration
    : TYPEE name=typee SEMICOLON
    ;

parameterized_typee_declaration
    : TYPEE name=typee LBRACE params=parameters_typee_declaration RBRACE
    ;

parameters_typee_declaration
    : (typee_definition SEMICOLON)+
    ;

// ----------------------------------------------------------------------------
// ---------------------------------- Typee -----------------------------------
typee
    : typee_refined
    | typee_abstraction_type
    | typee_definition
    | typee_basic_type
    | typee_type_abstract
    ;

typee_refined
    : LBRACE typeeRefined=typee PIPE condition=expression RBRACE
    ;

typee_abstraction_type
    : LPARENS argTypee=typee RARROW returnTypee=typee RPARENS
    ;

typee_definition
    : varName=IDENTIFIER COLON varTypee=typee
    ;

typee_basic_type
    : basicType=TYPEE_IDENTIFIER
    | basicType=ABSTRACT_TYPEE_IDENTIFIER
    ;

typee_type_abstract
    : abstractType=TYPEE_IDENTIFIER LBRACKET abstractParams=typee_abstract_parameters RBRACKET
    ;

typee_abstract_parameters
    : abstractParam=typee (COMMA restAbstractParams=typee)*
    ;

// ----------------------------------------------------------------------------
// --------------------------------- Function ---------------------------------
function
    : name=function_identifier LPARENS params=function_parameters? RPARENS RARROW returnType=typee where=function_where? body=function_body
    ;

function_identifier
    : name=IDENTIFIER (LBRACKET abstractParams=typee_abstract_parameters RBRACKET)?
    ;

function_parameters
    : typee (COMMA typee)*
    ;

function_where
    : WHERE LBRACE expression (AND expression)* RBRACE
    ;

// ----------------------------------------------------------------------------
// ------------------------------ Function Body -------------------------------
function_body
    : ASSIGN nativee=NATIVE SEMICOLON                    # NativeBody
    | ASSIGN uninterpreted=UNINTERPRETED SEMICOLON      # UninterpretedBody
    | LBRACE (statement SEMICOLON)* RBRACE              # RegularBody
    ;

statement
    : variable_definition
    | variable_assignment
    | if_statement
    | expression
    ;

variable_definition
    : variable=typee ASSIGN exp=expression
    ;

variable_assignment
    : variable=IDENTIFIER ASSIGN exp=expression
    ;

if_statement
    // Allows if true {native} else {native}, but no one will do that!
    : IF cond=expression then=function_body ELSE otherwise=function_body
    ;

expression
    : LPARENS expression RPARENS                                                                # Parenthesis
    | target=expression app=function_abstraction? LPARENS params=call_parameters? RPARENS       # FunctionCall
    | left=expression op=POWER right=expression                                                 # NumberExpression
    | op=(NOT | MINUS) right=expression                                                         # UnaryOperation
    | left=expression op=(MULT | QUOT | MODULE | POWER) right=expression                        # NumberExpression
    | left=expression op=(PLUS | MINUS) right=expression                                        # NumberExpression
    | left=expression op=(LT | LE | GT | GE) right=expression                                   # LogicalExpression
    | left=expression op=(EQUAL | DIFF) right=expression                                        # LogicalExpression
    | left=expression op=CONJUNCTION right=expression                                           # LogicalExpression
    | left=expression op=DISJUNCTION right=expression                                           # LogicalExpression
    | left=expression op=IMPLIE right=expression                                                # LogicalExpression
    | ABSTRACTION variable=typee RARROW exp=expression                                          # AbstractionExpression
    | cond=expression QUESTION then=expression COLON otherwise=expression                       # IfExpression
    | variable=IDENTIFIER (DOT attribute=IDENTIFIER)+                                           # TypeeAttributeCall
    | '?' typee? '?'                                                                            # Hole
    | variable=IDENTIFIER                                                                       # Variable
    | value=(INTEGER | FLOAT | BOOLEAN | STRING)                                                # Literal
    | improvement=(MAXIMIZE | MINIMIZE | EVALUATE) LPARENS param=expression RPARENS             # FitnessImprovement
    ;

function_abstraction
    : LBRACKET typee_abstract_parameters RBRACKET
    ;

call_parameters
    : expression (COMMA expression)*
    ;

// ----------------------------------------------------------------------------
// ---------------------------------- Lexer -----------------------------------
// Import
IMPORT: 'import'    ;
FROM: 'from'        ;

// If and Else
IF: 'if'        ;
ELSE: 'else'    ;
QUESTION: '?'   ;

// Improvements
MAXIMIZE: '@maximize' ;
MINIMIZE: '@minimize' ;
EVALUATE: '@evaluate' ;

// Number operations
PLUS: '+' 		;
MINUS: '-' 		;
MULT: '*' 		;
QUOT: '/'    	;
MODULE: '%' 	;
POWER: '^'      ;

// Logical Operators
CONJUNCTION: '&&'   ;
DISJUNCTION: '||'   ;
NOT: '!'            ;
PIPE: '|'           ;

// Logical Operators
LT: '<' 			;
LE: '<=' 			;
GT: '>' 			;
GE: '>=' 			;
EQUAL: '==' 		;
DIFF: '!='			;

ASSIGN: '='     ;

RARROW: '->'    ;
FATARROW: '=>'  ;
IMPLIE: '-->'   ;

LBRACE: '{'     ;
RBRACE: '}'     ;
LPARENS: '('    ;
RPARENS: ')'    ;
LBRACKET: '['   ;
RBRACKET: ']'   ;

// Typee
TYPEE: 'type'   ;
AS: 'as'        ;

// Dependent, Refined and Native
AND: 'and'          ;
WHERE: 'where'      ;
NATIVE: 'native'    ;
UNINTERPRETED: 'uninterpreted'    ;
ABSTRACTION: '\\'   ;

// Special Characters
DOTDOT: '..'    ;
DOT: '.'        ;
COLON: ':'      ;
COMMA: ','      ;
SEMICOLON: ';'  ;

// Literal values
BOOLEAN: 'true' | 'false';
INTEGER: ('0' | [1-9][0-9]*);
FLOAT: [0-9]*'.'?[0-9]+;
STRING: '"' ((~["\\\r\n] | '\\' [btnfr"'\\])+)? '"';

// Identifiers
IDENTIFIER: [a-z][_a-zA-Z0-9]*          ;
TYPEE_IDENTIFIER: [A-Z][_a-zA-Z0-9]+    ;
ABSTRACT_TYPEE_IDENTIFIER: [A-Z]        ;

// Comments
LINE_COMMENT: '//' ~[\r\n]* -> skip ;
BLOCK_COMMENT: '/*' .*? '*/' -> skip ;

// Ignorar espacos em brancos
WS:  [ \t\r\n]+ -> skip;
