%option yylineno
%pointer

%{
    #include <cstdlib>
    #include <cstring>
    #include "ast.hpp"
    #include "parser.hpp"

    /* void yyerror(const char *); */
%}

/** WRITE ME:
 *  Put any definitions you need here. Add your own regular expressions
 *  below for ALL tokens defined in the manual. You can choose not to use
 *  definitions here.
 */

/* HERE */

/** The example below is very simple, but it shows almost everything you will
 *  need to do for this first part. The syntax is as follows:
 *
 *  regular_expression      {  c code  }
 *
 * The lexer will try to match each regular expression. When it does it will
 * execute the corresponding C code.
*/

%%

[ \t\n]+  ; /* skip whitespace */
boolean   { return BOOLEAN; }
char      { return CHAR; }
integer   { return INTEGER; }
string    { return STRING; }
intptr    { return INTPTR; }
charptr   { return CHARPTR; }
if        { return IF; }
else      { return ELSE; }
while     { return WHILE; }
var       { return VAR; }
procedure { return PROCEDURE; }
return    { return RETURN; }
null      { return N; }

"&&"  { return ANDAND; }
"/"   { return SLASH; }
"="   { return EQUAL; }
"=="  { return EQUALEQUAL; }
">"   { return GREATER; }
">="  { return GREATEREQUAL; }
"<"   { return LESS; }
"<="  { return LESSEQUAL; }
"-"   { return MINUS; }
"!"   { return BANG; }
"!="  { return BANGEQUAL; }
"||"  { return OROR; }
"+"   { return PLUS; }
"*"   { return TIMES; }
"&"   { return AND; }
"^"   { return CARET; }

true     { yylval.u_base_int = 1; return BOOLEAN_LITERAL; }
false    { yylval.u_base_int = 0; return BOOLEAN_LITERAL; }
'.'      { yylval.u_base_int=(int)(*(yytext+1)); return CHAR_LITERAL; }
\".*\"   { char * x = strdup(yytext) + 1; x[strlen(x)-1] = 0; yylval.u_base_charptr = x; return STRING_LITERAL; }

[a-zA-Z]([a-zA-Z_]|[0-9])* {yylval.u_base_charptr = strdup(yytext); return IDENTIFIER; }

[1-9][0-9]*|0        {yylval.u_base_int=strtol(yytext,NULL,10); return INTEGER_LITERAL; }
(0x|0X)[A-F0-9]*     {yylval.u_base_int=strtol(yytext,NULL,16); return INTEGER_LITERAL; }
0[0-7]*              {yylval.u_base_int=strtol(yytext,NULL,8); return INTEGER_LITERAL; }
[0-1][0-1]*b         {yylval.u_base_int=strtol(yytext,NULL,2); return INTEGER_LITERAL; }


";"   { return SEMICOLON; }
":"   { return COLON; }
","   { return COMMA; }
"|"   { return BAR; }
"{"   { return LCURLY; }
"}"   { return RCURLY; }
"("   { return LPAREN; }
")"   { return RPAREN; }
"["   { return LSQUARE; }
"]"   { return RSQUARE; }

"/%"((%+[^"/%"])|([^%]))*%*"%/" {/* Not cool, this was way too hard */}
.     { return BROKEN; }

%%

int yywrap(void) {
    return 1;
}
