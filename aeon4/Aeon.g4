/**
 * Grammar for the Aeon language
 * To compile the grammar: java -jar antlr-4.7.2-complete.jar -Dlanguage=Python3 -visitor -no-listener Aeon.g4
 */
grammar Aeon;

aeon
    : imprt* (typeeAlias | typeeDeclaration | function)* EOF ;

// Import
imprt
    : IMPORT path=importName SEMICOLON                              # RegularImport
    | IMPORT path=importName FROM functionName=IDENTIFIER SEMICOLON # SpecialImport
    ;

importName
    : name=(DOT | IDENTIFIER) (DOT importName)?;

// Type Alias
typeeAlias
    : TYPEE name=(IDENTIFIER | CLASS_NAME) AS typee SEMICOLON;

// Type declaration
typeeDeclaration
    : TYPEE (t_abs=IDENTIFIER FATARROW)? IDENTIFIER typee LBRACE (attribute | function)* RBRACE;

attribute
    : varName=IDENTIFIER COLON varType=typee SEMICOLON;

function
    : name=IDENTIFIER LPARENS params=parameters? RPARENS RARROW returnType=parameters (WHERE expression (AND expression)*)? ASSIGN (NATIVE | LBRACE body RBRACE) SEMICOLON;

parameters
    | (paramName=IDENTIFIER COLON)? typee                                          # SingleParameter
    | (paramName=IDENTIFIER COLON typee COMMA)? parameters                         # MultipleParameters
    ;

// paramName=IDENTIFIER COLON (typee | fAbstraction)
// todo:
typee
    : LPARENS typee RPARENS
    | LBRACE typee WHERE cond=expression RBRACE
    // | type_application
    // | fAbstraction
    | IDENTIFIER
    ;



fAbstraction : IDENTIFIER;

// Body of the expressions
body
    : varName=IDENTIFIER COLON varType=typee ASSIGN exp=expression body?              # BodyVarDefinition
    | varName=IDENTIFIER ASSIGN exp=expression body?                                  # BodyAssignment
    | expression body?                                                                # BodyExpression
    | IF cond=expression THEN then=expression ELSE elseBody=expression body?                        # IfThenElse
    | IF cond=expression LBRACE then=body RBRACE ELSE LBRACE elseBody=expression RBRACE body?       # IfThenElse
    ;


expression
    : LPARENS expression RPARENS                                                # Parenthesis
    | functionName=IDENTIFIER LPARENS (expression (COMMA expression)*)? RPARENS # FunctionCall
    | left=expression op=POWER right=expression                                 # BinaryOperationCall
    | op=(NOT | MINUS) right=expression                                         # UnaryOperationCall
    | left=expression op=(MULT | QUOTIENT | POWER) right=expression             # BinaryOperationCall
    | left=expression op=(PLUS | MINUS) right=expression                        # BinaryOperationCall
    | left=expression op=(LT | LE | GT | GE) right=expression                   # BinaryOperationCall
    | left=expression op=(EQUAL | DIFF | BEQUAL | BDIFF) right=expression       # BinaryOperationCall
    | left=expression op=CONJUNCTION right=expression                           # BinaryOperationCall
    | left=expression op=DISJUNCTION right=expression                           # BinaryOperationCall
    | ABSTRACTION varName=IDENTIFIER COLON varType=typee RARROW exp=expression  # Abstraction
    | IDENTIFIER                                                                # Variable
    | value=(INTEGER | FLOAT | BOOLEAN | STRING | HOLE)                         # Literal
    ;

// todo: typee, fAbstraction


// ---------------------------------- Lexer -----------------------------------
// Import rules
IMPORT: 'import';
FROM: 'from';

// Type alias rules
TYPEE: 'type';
AS: 'as';

// If then else
IF: 'if';
THEN: 'then';
ELSE: 'else';

// Dependent and Refined type rules
AND: 'and';
WHERE: 'where';
NATIVE: 'native';
ABSTRACTION: '\\';

// Special Characters
DOT: '.';
COLON: ':';
COMMA: ',';
SEMICOLON: ';';

ASSIGN: '=';

RARROW: '->';
FATARROW: '=>';
IMPLIE: '--->';

LBRACE: '{';
RBRACE: '}';
LPARENS: '(';
RPARENS: ')';
LBRACKET: '[';
RBRACKET: ']';
// LGUILLEMETS: '<';
// RGUILLEMETS: '>';

HOLE: '_?_';

PLUS: '+' 		;
MINUS: '-' 		;
MULT: '*' 		;
QUOTIENT: '/' 	;
MODULE: '%' 	;
POWER: '^'      ;

CONJUNCTION: '&&' ;
DISJUNCTION: '||'  ;
NOT: '!'  ;

// Logical Operators
LT: '<' 			;
LE: '<=' 			;
GT: '>' 			;
GE: '>=' 			;
EQUAL: '==' 		;
DIFF: '!='			;
BEQUAL: '===' 		;
BDIFF: '!=='		;


// Literal values
BOOLEAN: 'true' | 'false';
INTEGER: ('0' | '-'? [1-9][0-9]*);
FLOAT: '-'?[0-9]*'.'?[0-9]+;
STRING: '"' ((~["\\\r\n] | '\\' [btnfr"'\\])+)? '"';

// Variables
IDENTIFIER: [a-zA-Z][_a-zA-Z0-9]* ;
CLASS_NAME: [a-zA-Z][_a-zA-Z0-9]* '<' [a-zA-Z] '>' ;

// Comments
LINE_COMMENT: '//' ~[\r\n]* -> skip ;
BLOCK_COMMENT: '/*' .*? '*/' -> skip ;

// Ignorar espacos em brancos
WS:  [ \t\r\n]+ -> skip;
