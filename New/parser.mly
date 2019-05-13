/* File parser.mly */
%{
    open Expression
%}

%token LP RP COLON EQUAL CALL RET EOL EOF COMMA
%token <int> INT
%token <string> VAR
%token <string> FUNC
%start main             /* the entry point */
%type <Expression.expr_tree> main                     /* Specifying the type to be returned for the grammar symbol main */
%%
main:
    RET							   { Return }
    | VAR COLON EQUAL constant     {Assign(Var($1),$4)}
    | CALL function1 tuple		   {Call($2,$3)}
   	| constant					   {$1}
   	|function1					   {$1}
    | EOF                          { NULL }
;
function1:
	FUNC							{F($1)}
;
tuple:
	LP constant RP					{[$2]}
	|LP constantlist RP 			{$2}
;
constantlist:
	constantlist COMMA constant		{$1@[$3]}
	|constant COMMA constant		{[$1]@[$3]}
;
constant:
    VAR                             { Var($1) }      /* To be interpreted as a variable name with string as tokenised */
    | INT                           { Int($1) }      /* To be interpreted as an integer with its value as tokenised   */
;


/*TODO
 * Add support in the grammar for parenthesis
 *  - Adding the parenthesis should be able to change the parse tree to effectively modify precedence.
 *  E.g. 1+2*3  ==>        PLUS
 *                        /    \
 *                      NUM1   INTO
 *                            /    \
 *                         NUM 2  NUM 3
 *
 *  vs (1+2)*3  ==>        INTO
 *                        /    \
 *                     PLUS     NUM 3
 *                    /    \
 *                 NUM 1   NUM 2
 *
 * Try completing the calculator for basic arithmetic by adding division and subtraction, while respecting precedence
 * This will require changes right from the lexer.mll and parser.mly to the definition of print and evaluation functions in expression.ml
 *
 * ADVANCED
 * Try creating an expression for assigning new variables in the variable_set in the expression.ml file, so that they can be reused in a later evaluation statement.
 * E.g. myVar:=4.
 *      // Stores the integer value 4 corresponding to the string myVar in variable_set
 *
 *      myVar*3+1
 *      Answer: 13
 * */
