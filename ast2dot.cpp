#include "ast.hpp"
#include "symtab.hpp"
#include "primitive.hpp"

#include <cstdio>
#include <stack>

class Ast2dot : public Visitor
{
    private:
    FILE *m_out;        // File for writting output
    int count;          // Used to give each node a uniq id
    std::stack<int> s;  // Stack for tracking parent/child pairs

    public:

    Ast2dot(FILE* out)
    {
       count = 0;
       s.push(0);
       m_out = out;
       std::fprintf(m_out, "digraph G { page=\"8.5,11\"; size=\"7.5, 10\"; \n");
    }

    void finish()
    {
        std::fprintf(m_out, "}\n");
    }

    void add_edge(int p, int c)
    {
        std::fprintf(m_out, "\"%d\" -> \"%d\"\n", p, c);
    }

    void add_node(int c, const char* n)
    {
        std::fprintf(m_out, "\"%d\" [label=\"%s\"]\n" , c, n);
    }

    void draw(const char* n, Visitable* p)
    {
       count++;                         // Each node gets a unique number
       add_edge(s.top(), count);        // From parent to this
       add_node(count, n);              // Name the this node
       s.push(count);                   // This node is the parent
       p->visit_children(this);
       s.pop();                         // Restore old parent
    }

    void draw_symname(const char* n, SymName* p)
    {
       count++;                         // Each node gets a unique number
       add_edge(s.top(), count);        // From parent to this
       // Print symname strings
       std::fprintf(m_out, "\"%d\" [label=\"%s\\n\\\"%s\\\"\"]\n" , count, n, p->spelling());
    }

    void draw_primitive(const char* n, Primitive* p)
    {
       count++;                         // Each node gets a unique number
       add_edge(s.top(), count);        // From parent to this
       std::fprintf(m_out, "\"%d\" [label=\"%s\\n%d\"]\n" , count, n, p->m_data);
    }

    void draw_string_primitive(const char* n, StringPrimitive* p)
    {
       count++;                         // Each node gets a unique number
       add_edge(s.top(), count);        // From parent to this
       std::fprintf(m_out, "\"%d\" [label=\"%s\\n\\\"%s\\\"\"]\n" , count, n, p->m_string);
    }

    void visitProgramImpl(ProgramImpl *p) { draw("ProgramImpl", p); }
    void visitProcImpl(ProcImpl *p) { draw("ProcImpl", p); }
    void visitProcedure_blockImpl(Procedure_blockImpl *p) { draw("ProcedureBlockImpl", p); }
    void visitNested_blockImpl(Nested_blockImpl *p) { draw("NestedBlockImpl", p); }
    void visitDeclImpl(DeclImpl *p) { draw("DeclImpl", p); }
    void visitAssignment(Assignment *p) { draw("Assignment", p); }
    void visitStringAssignment(StringAssignment *p) { draw("StringAssignment", p); }
    void visitCall(Call *p) { draw("Call", p); }
    void visitReturn(Return *p) { draw("Return", p); }
    void visitIfNoElse(IfNoElse *p) { draw("IfNoElse", p); }
    void visitIfWithElse(IfWithElse *p) { draw("IfWithElse", p); }
    void visitWhileLoop(WhileLoop *p) { draw("WhileLoop", p); }
    void visitCodeBlock(CodeBlock *p) { draw("CodeBlock", p); }

    void visitTInteger(TInteger *p) { draw("TInteger", p); }
    void visitTIntPtr(TIntPtr *p) { draw("TIntPtr", p); };
    void visitTBoolean(TBoolean *p) { draw("TBoolean", p); }
    void visitTCharacter(TCharacter *p) { draw("TCharacter", p); }
    void visitTCharPtr(TCharPtr *p) { draw("TCharPtr", p); };
    void visitTString(TString *p) { draw("TString", p); }

    void visitAbsoluteValue(AbsoluteValue *p) { draw("AbsoluteValue", p); };
    void visitAddressOf(AddressOf *p) { draw("AddressOf", p); };
    void visitAnd(And *p) { draw("And", p); }
    void visitDiv(Div *p) { draw("Div", p); }
    void visitCompare(Compare *p) { draw("Compare", p); }
    void visitGt(Gt *p) { draw("Gt", p); }
    void visitGteq(Gteq *p) { draw("Gteq", p); }
    void visitLt(Lt *p) { draw("Lt", p); }
    void visitLteq(Lteq *p) { draw("Lteq", p); }
    void visitMinus(Minus *p) { draw("Minus", p); }
    void visitNoteq(Noteq *p) { draw("Noteq", p); }
    void visitOr(Or *p) { draw("Or", p); }
    void visitPlus(Plus *p) { draw("Plus", p); }
    void visitTimes(Times *p) { draw("Times", p); }
    void visitNot(Not *p) { draw("Not", p); }
    void visitUminus(Uminus *p) { draw("Uminus", p); }

    void visitIdent(Ident *p) { draw("Ident", p); }
    void visitArrayAccess(ArrayAccess *p) { draw("ArrayAccess", p); }
    void visitIntLit(IntLit *p) { draw("IntLit", p); }
    void visitCharLit(CharLit *p) { draw("CharLit", p); }
    void visitBoolLit(BoolLit *p) { draw("BoolLit", p); }
    void visitNullLit(NullLit *p) { draw("NullLit", p); }

    /* LHS */
    void visitDeref(Deref *p) { draw("Deref", p); };
    void visitVariable(Variable *p) { draw("Variable", p); };
    void visitDerefVariable(DerefVariable *p) { draw("DerefVariable", p); };
    void visitArrayElement(ArrayElement *p) { draw("ArrayElement", p); };

    // Special cases
    void visitSymName(SymName *p) { draw_symname("SymName",p); }
    void visitPrimitive(Primitive *p) { draw_primitive("Primitive",p); }
    void visitStringPrimitive(StringPrimitive *p) { draw_string_primitive("StringPrimitive",p); }
};

void dopass_ast2dot(Program_ptr ast)
{
    Ast2dot* ast2dot = new Ast2dot(stdout);     // Create new visitor
    ast->accept(ast2dot);                       // Walk the tree with the visitor above
    ast2dot->finish();                          // Finalize printout
    delete ast2dot;
}
