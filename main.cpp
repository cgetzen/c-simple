/**
 *  This file is provided for you to run your parser.  You should not have
 *  to edit anything if you did the yacc, lex, and typecheck.cpp files
 *  correctly. All this file does is calls yyparse() and uses the visitor
 *  class to typecheck and print the graph.
 */

#include "ast.hpp"
#include "parser.hpp"
#include "symtab.hpp"
#include "primitive.hpp"
#include <assert.h>

extern int yydebug;
extern int yyparse();

// This is defined in ast2dot.cpp
void dopass_ast2dot(Program_ptr ast);

// This is defined in typecheck.cpp
void dopass_typecheck(Program_ptr ast, SymTab* st);

// This is defiend in codegen.cpp
void dopass_codegen(Program_ptr ast, SymTab* st);

// Make sure to set this to the final // syntax tree in parser.ypp
Program_ptr ast;
int main(void)
{
    yydebug = 0;    // Set yydebug to 1 if you want yyparse() to dump a trace
    yyparse();

    SymTab st;      // Symbol Table
    if(ast) {       // Walk over the ast
        dopass_typecheck(ast, &st);
        // dopass_ast2dot(ast);
        dopass_codegen(ast, &st);
    }

    return 0;
}
