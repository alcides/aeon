/**
 * Grammar for the Aeon language
 * To compile the grammar: java -jar antlr-4.7.2-complete.jar -Dlanguage=Python3 -visitor -no-listener -o generated Aeon.g4
 */
grammar Aeon;

aeon
    : imprt* (typeeDeclaration | typeeAlias | function)* EOF ;

// Import
imprt
    : IMPORT path=importName SEMICOLON                              # RegularImport
    | IMPORT functionName=dottedName FROM path=importName SEMICOLON # SpecialImport
    ;

importName
    : name=(DOT | IDENTIFIER) (DOT importName)?;

// Type Alias
typeeAlias
    : TYPEE name=typee AS alias=typee SEMICOLON;

// Type declaration
typeeDeclaration
    : TYPEE name=typee (LBRACE (attr=typee SEMICOLON)+ RBRACE | SEMICOLON);

function
    : DEFINE name=dottedName COLON LPARENS params=parameters? RPARENS RARROW returnType=typee (WHERE LBRACE expression (AND expression)* RBRACE)? (ASSIGN native=NATIVE SEMICOLON | LBRACE body RBRACE);

parameters 
    : param=typee (COMMA restParams=parameters)?;

// Types
typee
    : LBRACE typee PIPE cond=expression RBRACE      # TypeeCondition
    | type1=typee RARROW type2=typee                # TypeeAbstraction
    | varName=IDENTIFIER COLON typed=typee          # TypeeBasicType
    | name=IDENTIFIER (LT tabst=abstrParams GT)?    # TypeeAbstractionApplication
    ;

// Body of the expressions
body
    : varType=typee ASSIGN exp=expression SEMICOLON nextExpr=body?                                  # BodyVarDefinition
    | varName=IDENTIFIER ASSIGN exp=expression SEMICOLON nextExpr=body?                             # BodyAssignment
    | IF cond=expression LBRACE then=body RBRACE ELSE LBRACE elseBody=body RBRACE nextExpr=body?    # IfThenElse
    | expr=expression SEMICOLON nextExpr=body?                                                      # BodyExpression
    ;

expression
    : LPARENS expression RPARENS                                                                    # Parenthesis
    | functionName=dottedName LPARENS (param=expression (COMMA params=expression)*)? RPARENS        # FunctionCall
    | left=expression op=POWER right=expression                                                     # BinaryOperationCall
    | left=expression op=IMPLIE right= expression                                                   # BinaryOperationCall
    | op=(NOT | MINUS) right=expression                                                             # UnaryOperationCall
    | left=expression op=(MULT | QUOTIENT | POWER) right=expression                                 # BinaryOperationCall
    | left=expression op=(PLUS | MINUS) right=expression                                            # BinaryOperationCall
    | left=expression op=(LT | LE | GT | GE) right=expression                                       # BinaryOperationCall
    | left=expression op=(EQUAL | DIFF | BEQUAL | BDIFF) right=expression                           # BinaryOperationCall
    | left=expression op=CONJUNCTION right=expression                                               # BinaryOperationCall
    | left=expression op=DISJUNCTION right=expression                                               # BinaryOperationCall
    | ABSTRACTION varType=typee RARROW exp=expression                                               # Abstraction
    | IF cond=expression THEN then=expression ELSE elseBody=expression                              # IfThenElseExpr
    | varName=IDENTIFIER                                                                            # Variable
    | value=(INTEGER | FLOAT | BOOLEAN | STRING | HOLE)                                             # Literal
    ;

// ---------- Helper parser rules
dottedName : name=IDENTIFIER (LT tabst=abstrParams GT)? (DOT dotted=IDENTIFIER)? ;

abstrParams : param=typee (COMMA restParams=abstrParams)? ;

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
DEFINE: 'define';
ABSTRACTION: '\\';

// Special Characters
DOT: '.';
COLON: ':';
COMMA: ',';
SEMICOLON: ';';

ASSIGN: '=';

RARROW: '->';
FATARROW: '=>';
IMPLIE: '-->';

LBRACE: '{';
RBRACE: '}';
LPARENS: '(';
RPARENS: ')';
LBRACKET: '[';
RBRACKET: ']';
// LGUILLEMETS: '<';
// RGUILLEMETS: '>';

HOLE: '[]';

PLUS: '+' 		;
MINUS: '-' 		;
MULT: '*' 		;
QUOTIENT: '/' 	;
MODULE: '%' 	;
POWER: '^'      ;

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
BEQUAL: '===' 		;
BDIFF: '!=='		;


// Literal values
BOOLEAN: 'true' | 'false';
INTEGER: ('0' | [1-9][0-9]*);
FLOAT: [0-9]*'.'?[0-9]+;
STRING: '"' ((~["\\\r\n] | '\\' [btnfr"'\\])+)? '"';

// Variables
IDENTIFIER: [a-zA-Z][_a-zA-Z0-9]* ;

// Comments
LINE_COMMENT: '//' ~[\r\n]* -> skip ;
BLOCK_COMMENT: '/*' .*? '*/' -> skip ;

// Ignorar espacos em brancos
WS:  [ \t\r\n]+ -> skip;
