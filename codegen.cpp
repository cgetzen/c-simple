#include <iostream>
#include <cassert>
#include <typeinfo>

#include "ast.hpp"
#include "symtab.hpp"
#include "primitive.hpp"

#define O stdout
#define D stderr
#define DEBUG(...) do {fprintf(D, "\t\t\t"); fprintf(D, __VA_ARGS__); fprintf(D, "\n"); } while(0)
#define OUTPUT(...) do { fprintf(O, __VA_ARGS__); fprintf(O, "\n"); } while(0)

#define default_rule(X)  X->m_attribute.m_scope = m_st->get_scope(); \
      X->visit_children(this);

using namespace std;

class Codegen : public Visitor
{
  private:
    FILE* m_outputfile;
    SymTab *m_st;

    // Basic size of a word (integers and booleans) in bytes
    static const int wordsize = 4;

    int label_count; // Access with new_label

    // Helpers
    // This is used to get new unique labels (cleverly names label1, label2, ...)
    int new_label()
    {
        return label_count++;
    }

    void set_text_mode()
    {
        fprintf(m_outputfile, ".text\n\n");
    }

    void set_data_mode()
    {
        fprintf(m_outputfile, ".data\n\n");
    }

    // PART 1:
    // 1) get arithmetic expressions on integers working:
    //  you wont really be able to run your code,
    //  but you can visually inspect it to see that the correct
    //  chains of opcodes are being generated.
    // 2) get procedure calls working:
    //  if you want to see at least a very simple program compile
    //  and link successfully against gcc-produced code, you
    //  need to get at least this far
    // 3) get boolean operation working
    //  before we can implement any of the conditional control flow
    //  stuff, we need to have booleans worked out.
    // 4) control flow:
    //  we need a way to have if-elses and while loops in our language.
    // 5) arrays: just like variables, but with an index

    // Hint: the symbol table has been augmented to track an offset
    //  with all of the symbols.  That offset can be used to figure
    //  out where in the activation record you should look for a particuar
    //  variable


    ///////////////////////////////////////////////////////////////////////////////
    //
    //  function_prologue
    //  function_epilogue
    //
    //  Together these two functions implement the callee-side of the calling
    //  convention.  A stack frame has the following layout:
    //
    //                         <- SP (before pre-call / after epilogue)
    //  high -----------------
    //       | actual arg 1  |
    //       |    ...        |
    //       | actual arg n  |
    //       -----------------
    //       |  Return Addr  |
    //       =================
    //       | temporary 1   | <- SP (when starting prologue)
    //       |    ...        |
    //       | temporary n   |
    //   low ----------------- <- SP (when done prologue)
    //
    //
    //              ||
    //              ||
    //             \  /
    //              \/
    //
    //
    //  The caller is responsible for placing the actual arguments
    //  and the return address on the stack. Actually, the return address
    //  is put automatically on the stack as part of the x86 call instruction.
    //
    //  On function entry, the callee
    //
    //  (1) allocates space for the callee's temporaries on the stack
    //
    //  (2) saves callee-saved registers (see below) - including the previous activation record pointer (%ebp)
    //
    //  (3) makes the activation record pointer (frmae pointer - %ebp) point to the start of the temporary region
    //
    //  (4) possibly copies the actual arguments into the temporary variables to allow easier access
    //
    //  On function exit, the callee:
    //
    //  (1) pops the callee's activation record (temporay area) off the stack
    //
    //  (2) restores the callee-saved registers, including the activation record of the caller (%ebp)
    //
    //  (3) jumps to the return address (using the x86 "ret" instruction, this automatically pops the
    //      return address off the stack
    //
    //////////////////////////////////////////////////////////////////////////////
    //
    // Since we are interfacing with code produced by GCC, we have to respect the
    // calling convention that GCC demands:
    //
    // Contract between caller and callee on x86:
    //    * after call instruction:
    //           o %eip points at first instruction of function
    //           o %esp+4 points at first argument
    //           o %esp points at return address
    //    * after ret instruction:
    //           o %eip contains return address
    //           o %esp points at arguments pushed by caller
    //           o called function may have trashed arguments
    //           o %eax contains return value (or trash if function is void)
    //           o %ecx, %edx may be trashed
    //           o %ebp, %ebx, %esi, %edi must contain contents from time of call
    //    * Terminology:
    //           o %eax, %ecx, %edx are "caller save" registers
    //           o %ebp, %ebx, %esi, %edi are "callee save" registers
    ////////////////////////////////////////////////////////////////////////////////


    void emit_prologue(SymName *name, unsigned int size_locals, unsigned int num_args)
    {
      DEBUG("Number of args: %d", num_args);
      OUTPUT("%s:", name->spelling());

      // Store previous base pointer (ebp) of caller on stack
      OUTPUT("\tpushl %%ebp");
      OUTPUT("\tmovl %%esp, %%ebp");
      if(size_locals) OUTPUT("\tsubl $%d, %%esp", size_locals);

      // Copy args to local
      for(uint i=0; i<num_args; ++i){
        OUTPUT("\tmovl %d(%%ebp), %%ebx", (2+i)*wordsize);
        OUTPUT("\tmovl %%ebx, %d(%%ebp)", -4*(i+1));
      }
      OUTPUT("\tpushl %%ebx");
    }

    void emit_epilogue() {
      OUTPUT("\tmovl %%ebp, %%esp");
      OUTPUT("\tpopl %%ebp");
      OUTPUT("\tretl");
    }
    void emit_equality(Compare * p, bool equal, bool lt, bool gt){
      char c;
      if(equal) c = 'e'; else c = ' ';
      int label1 = new_label(), label2 = new_label();
      OUTPUT("\tpop %%eax");
      OUTPUT("\tpop %%ebx");
      OUTPUT("\tcmp %%eax, %%ebx");
      if(equal && !lt && !gt) OUTPUT("\tje label%d", label1);
      if(!equal && !lt && !gt) OUTPUT("\tjne label%d", label1);
      if(gt) OUTPUT("\tjg%c label%d", c, label1);
      if(lt) OUTPUT("\tjl%c label%d", c, label1);
      OUTPUT("\tpush $0");
      OUTPUT("\tjmp label%d", label2);
      OUTPUT("label%d:", label1);
      OUTPUT("\tpush $1");
      OUTPUT("label%d:", label2);
    }

  public:

    Codegen(FILE* outputfile, SymTab* st)
    {
        m_outputfile = outputfile;
        m_st = st;
        label_count = 0;
    }

    void visitProgramImpl(ProgramImpl* p) {
      DEBUG("visitProgramImpl");
      OUTPUT(".text\n");
      for(auto iter = p->m_proc_list->begin(); iter != p->m_proc_list->end(); ++iter){
        //OUTPUT( ((ProcImpl *)(*iter))->m_symname->spelling() );
      }
      OUTPUT(".globl Main\n");
      default_rule(p);
    }

    void visitProcImpl(ProcImpl* p) {
      DEBUG("visitProcImpl");
      SymName * name = p->m_symname;

      DEBUG("Scopesize addr: %p", p->m_procedure_block->m_attribute.m_scope);
      DEBUG("Scopesize: %i", m_st->scopesize(p->m_procedure_block->m_attribute.m_scope));
      unsigned int size_locals =  m_st->scopesize(p->m_procedure_block->m_attribute.m_scope);
      unsigned int num_args = 0;
    //  for(auto iter = p->m_decl_list->begin(); iter != p->m_decl_list->end(); ++iter)
    //    num_args += ((DeclImpl *)(*iter))->m_symname_list->size();
      for(Decl *  n : *p->m_decl_list)
        num_args += ((DeclImpl *)(n))->m_symname_list->size();
      DEBUG("num_args: %d", num_args);
      emit_prologue(name, size_locals, num_args);


      default_rule(p)

      emit_epilogue();
      //OUTPUT("%s:", p->m_symname->spelling());
      //OUTPUT( p->m_symname->spelling() ); OUTPUT( ":\n");
    }

    void visitProcedure_blockImpl(Procedure_blockImpl* p) {
      DEBUG("visitProcedure_blockImpl");
      default_rule(p);
    }

    void visitNested_blockImpl(Nested_blockImpl* p) {
      DEBUG("visitNested_blockImpl");
    }

    void visitAssignment(Assignment* p) {
      DEBUG("visitAssignment");
      //default_rule(p);

      p->m_expr->accept(this);
      p->m_lhs->accept(this);


      DEBUG("SCOPE: %p", p->m_lhs->m_attribute.m_scope);
      //Symbol * s = m_st->lookup(p->m_lhs->m_attribute.m_scope,  "x");
      Symbol * s =m_st->lookup(p->m_lhs->m_attribute.m_scope, static_cast<Variable *>(p->m_lhs)->m_symname->spelling());
      //int i = -4 - s->get_offset();

      DEBUG("NAME: %s", static_cast<Variable *>(p->m_lhs)->m_symname->spelling());
      DEBUG("SYMBOL ADDRESS %p", s);
      DEBUG("OFFSET: %i", s->get_offset());

      // if(s->m_basetype == bt_string){
      //   int xx=4+s->get_offset();
      //   OUTPUT("\tpop %%eax");
      //   OUTPUT("Here:")
      //   OUTPUT("")
      //   OUTPUT("\tmov %%eax, -%d(%%ebp)", (-xx+(-1)*4*((IntLit*)p->m_lhs)->m_primitive->m_data));
      // } else {
    //  OUTPUT("labelasdf:");
      OUTPUT("\tpopl %%ecx"); // Left Hand Side
      //OUTPUT("\tpopl %%ebx");
      OUTPUT("popl %%eax"); // Right Hand Side
      //OUTPUT("pushl %%ecx");
      //OUTPUT("pushl %%ebx");

      // OUTPUT("popl %%ebx");

      //OUTPUT("addl %%ebp, %%ecx");
      //OUTPUT("neg %%ecx");
      //OUTPUT("addl %%ebp, %%ecx");
      int x = new_label();
      OUTPUT("Asdf%d:", x);
      if(p->m_lhs->m_attribute.m_basetype == bt_char){
        OUTPUT("movb %%al, (%%ecx)");
      } else if (p->m_lhs->m_attribute.m_basetype == bt_string) {
        for(uint x = 0; x < s->m_string_size-4; x++){
          OUTPUT("movb %%al, -%d(%%ecx)", x);
          OUTPUT("popl %%eax");
        }
        OUTPUT("pushl %%eax");
      } else {
        OUTPUT("movb %%al, (%%ecx)");
        OUTPUT("shrl $8, %%eax");
        OUTPUT("movb %%al, 1(%%ecx)");
        OUTPUT("shrl $8, %%eax");
        OUTPUT("movb %%al, 2(%%ecx)");
        OUTPUT("shrl $8, %%eax");
        OUTPUT("movb %%al, 3(%%ecx)");
      }

      //}
    }

    void visitCall(Call* p) {
      DEBUG("visitCall");
      default_rule(p);
      int n = p->m_expr_list->size() * wordsize;
      Symbol * x = m_st->lookup(p->m_attribute.m_scope, p->m_symname->spelling());
      DEBUG("%s", p->m_symname->spelling());
      OUTPUT("\tcall %s", p->m_symname->spelling());
      OUTPUT("\taddl $%d, %%esp", n);
      DEBUG("%d", x->get_offset());
      OUTPUT("popl %%ebx");

      OUTPUT("\tmovl %%eax, (%%ebx)");//, -%d(%%ebp)", x->get_offset()+4);

    }

    void visitReturn(Return* p) {
      DEBUG("visitReturn");
      default_rule(p);
      OUTPUT("\tpop %%eax");
    }

    // Control flow

    void visitIfNoElse(IfNoElse* p) {
      DEBUG("visitIfNoElse");

      int label = new_label();
      p->m_expr->accept(this);
      OUTPUT("\tpop %%eax");
      OUTPUT("\tcmp $0, %%eax");
      OUTPUT("\tje label%d", label);
      p->m_nested_block->visit_children(this);
      OUTPUT("\tlabel%d:", label);
    }

    void visitIfWithElse(IfWithElse* p) {
      int label_1 = new_label(), label_2 = new_label();
      DEBUG("visitIfNoElse");
      p->m_expr->accept(this);
      OUTPUT("\tpop %%eax");
      OUTPUT("\tcmp $1, %%eax");
      OUTPUT("\tjne label%d", label_1);
      p->m_nested_block_1->visit_children(this);
      OUTPUT("\tjmp label%d", label_2);
      OUTPUT("label%d:", label_1);
      p->m_nested_block_2->visit_children(this);
      OUTPUT("label%d:", label_2);
    }

    void visitWhileLoop(WhileLoop* p) {
      DEBUG("visitWhileLoop");
      int label_1 = new_label(), label_2 = new_label();
      OUTPUT("label%d:", label_1);
      p->m_expr->accept(this);
      OUTPUT("\tpop %%eax");
      OUTPUT("\tcmp $1, %%eax");
      OUTPUT("\tjne label%d", label_2);
      p->m_nested_block->visit_children(this);
      OUTPUT("\tjmp label%d", label_1);
      OUTPUT("label%d:", label_2);
    }

    void visitCodeBlock(CodeBlock *p) {
      DEBUG("visitCodeBlock");
      default_rule(p);
    }

    // Variable declarations (no code generation needed)
    void visitDeclImpl(DeclImpl* p)
    {
      DEBUG("visitDeclImpl");
      //default_rule(p);
    }

    void visitTInteger(TInteger* p)
    {
      DEBUG("visitTInteger");
    }

    void visitTIntPtr(TIntPtr* p)
    {
      DEBUG("visitTIntPtr");
    }

    void visitTBoolean(TBoolean* p)
    {
      DEBUG("visitTBoolean");
    }

    void visitTCharacter(TCharacter* p)
    {
      DEBUG("visitTCharacter");
    }

    void visitTCharPtr(TCharPtr* p)
    {
      DEBUG("visitTCharPtr");
    }

    void visitTString(TString* p)
    {
      DEBUG("visitTString");
    }

    // Comparison operations
    void visitCompare(Compare* p) {
      DEBUG("visitCompare");
      default_rule(p);
      emit_equality(p, true, false, false);
    }

    void visitNoteq(Noteq* p) {
      DEBUG("visitNoteq");
      default_rule(p);
      emit_equality((Compare *)(p), false, false, false);

    }

    void visitGt(Gt* p) {
      DEBUG("visitGT");
      default_rule(p);
      emit_equality((Compare *)(p), false, false, true);
    }

    void visitGteq(Gteq* p) {
      DEBUG("visitGteq");
      default_rule(p);
      emit_equality((Compare *)(p), true, false, true);
    }

    void visitLt(Lt* p) {
      DEBUG("visitLt");
      default_rule(p);
      emit_equality((Compare *)(p), false, true, false);
    }

    void visitLteq(Lteq* p) {
      DEBUG("visitLteq");
      default_rule(p);
      emit_equality((Compare *)(p), true, true, false);
    }

    // Arithmetic and logic operations
    void visitAnd(And* p) {
      DEBUG("visitAnd");
      default_rule(p);
      OUTPUT("popl %%eax");
      OUTPUT("popl %%ebx");
      OUTPUT("andl %%eax, %%ebx");
      OUTPUT("pushl %%ebx");
    }

    void visitOr(Or* p) {
      DEBUG("visitOr");
      default_rule(p);
      int label = new_label();
      OUTPUT("\tpop %%eax");
      OUTPUT("\tpop %%ebx");
      OUTPUT("\t%%ebx, %%eax");
      OUTPUT("cmp $0, %%eax");
      OUTPUT("je label%d", label);
      OUTPUT("movl $1, %%eax");
      OUTPUT("label%d:", label);
      OUTPUT("pushl %%eax");
    }

    void visitMinus(Minus* p) {
      DEBUG("visitMinus");
      p->m_expr_1->accept(this);
      p->m_expr_2->accept(this);
      OUTPUT("\tpopl %%eax");
      OUTPUT("\tpopl %%ebx");
      OUTPUT("\tsubl %%eax, %%ebx");
      OUTPUT("\tpushl %%ebx");
    }

    void visitPlus(Plus* p) {
      DEBUG("\tvisitPlus");
      default_rule(p);
      OUTPUT("\tpop %%eax");
      OUTPUT("\tpop %%ebx");
      OUTPUT("\tadd %%ebx, %%eax");
      OUTPUT("\tpush %%eax");
    }

    void visitTimes(Times* p) {
      DEBUG("visitTimes");
      default_rule(p);
      OUTPUT("popl %%eax"); // Right
      OUTPUT("popl %%ebx"); // Left
      OUTPUT("imull %%eax, %%ebx"); // Stored ebx
      OUTPUT("pushl %%ebx"); // Result
    }

    void visitDiv(Div* p) {
      DEBUG("visitDiv");
      default_rule(p);
      OUTPUT("movl $0, %%edx"); // Prevents Floating Point exception
      OUTPUT("popl %%ebx"); // bottom
      OUTPUT("popl %%eax"); // top
      OUTPUT("divl %%ebx"); // bottom
      OUTPUT("pushl %%eax"); // result
    }

    void visitNot(Not* p) {
      DEBUG("visitNot");
      default_rule(p);
      int label_1 = new_label(), label_2 = new_label();
      OUTPUT("pop %%eax");
      OUTPUT("cmp $0, %%eax");
      OUTPUT("je label%d", label_1);
      OUTPUT("push $0");
      OUTPUT("jmp label%d", label_2);
      OUTPUT("label%d:", label_1);
      OUTPUT("push $1");
      OUTPUT("label%d:", label_2);

    }

    void visitUminus(Uminus* p) {
      DEBUG("visitUminus");
      default_rule(p);
      OUTPUT("\tpopl %%eax");
      OUTPUT("\tmovl %%eax, %%ebx");
      OUTPUT("\tsub %%ebx, %%eax");
      OUTPUT("\tsub %%ebx, %%eax");
      OUTPUT("\tpushl %%eax");
    }

    // Variable and constant access
    void visitIdent(Ident* p) {
      DEBUG("visitIdent");
      //p->m_symname->accept(this);
      //default_rule(p);
      //DEBUG("h");

      Symbol * s = m_st->lookup(p->m_attribute.m_scope, p->m_symname->spelling());
      OUTPUT("ident%d: #%d", new_label(), s->m_string_size-4);
      if(s->m_basetype == bt_char){
          OUTPUT("movl -%d(%%ebp), %%eax", s->get_offset()+4);
          OUTPUT("and $255, %%eax");
          OUTPUT("push %%eax");
      } else if(s->m_basetype == bt_string){
          OUTPUT("visitIdent%d:", new_label());
          for(uint i = 0; i < s->m_string_size-4; i++){
            OUTPUT("movl -%d(%%ebp), %%eax", s->get_offset()+ 4 +s->m_string_size-4 -1 - i);
            OUTPUT("and $255, %%eax");
            OUTPUT("push %%eax");
          }
      } else {
        OUTPUT("\tpush -%d(%%ebp)", s->get_offset() + 4);
      }
    }

    void visitBoolLit(BoolLit* p) {
      DEBUG("visitBoolLit");
      OUTPUT("\tpush $%d", p->m_primitive->m_data);
    }

    void visitCharLit(CharLit* p) {
      DEBUG("visitCharLit");
      OUTPUT("\tpush $%d", p->m_primitive->m_data);
    }

    void visitIntLit(IntLit* p) {
      DEBUG("visitIntLit");
      int x = new_label();
      OUTPUT("la%d:",x );
      OUTPUT("\tpush $%d", p->m_primitive->m_data);
      //OUTPUT("pop %%eax");
      //OUTPUT("push %%eax");
    }

    void visitNullLit(NullLit* p) {
      DEBUG("visitNullLit");
      OUTPUT("\tpush $0");
    }

    void visitArrayAccess(ArrayAccess* p) {
      DEBUG("visitArrayAccess");
      //default_rule(p);
      //Symbol *s = m_st->lookup(p->m_attribute.m_scope, p->m_symname->spelling());
      //DEBUG("%p", s);
      p->m_expr->accept(this);
      DEBUG(p->m_symname->spelling());
      DEBUG("%p", p->m_attribute.m_scope);
      DEBUG("%s", p->m_symname->spelling());
      //int x = m_st->lookup(p->m_attribute.m_scope, p->m_symname->spelling())->get_size();

      //OUTPUT("popl %%eax\n");
      //OUTPUT("imul $4, %%eax");
      //OUTPUT("movl %%ebp, %%ebx");
      //OUTPUT("subl $%d, %%ebp", 4);// (x + (m_st->lookup(p->m_attribute.m_scope, p->m_symname->spelling()))->get_size());//here
      //OUTPUT("addl %%eax, %%ebp");
      //OUTPUT("pushl 0(%%ebp)");
      //OUTPUT("movl %%ebx, %%ebp");
      Symbol *s=m_st->lookup(p->m_attribute.m_scope, p->m_symname->spelling());
      DEBUG("VISITARRAYACCESS POINTER: %p", s);
      OUTPUT("pop %%eax");
      //OUTPUT("imul $4, %%eax");
      OUTPUT("neg %%eax");
      OUTPUT("addl $%d, %%eax", s->get_offset()+4+s->m_string_size-4-1);
      OUTPUT("subl %%ebp, %%eax");
    //  OUTPUT("visitArray:");
      OUTPUT("negl %%eax");
      OUTPUT("movl (%%eax), %%eax");
      OUTPUT("and $255, %%eax");
      OUTPUT("pushl %%eax");
    }

    // LHS
    void visitVariable(Variable* p)
    {
      DEBUG("visitVariable");
      //default_rule(p);
      Symbol* s = m_st->lookup(p->m_attribute.m_scope, p->m_symname->spelling());
      int x = new_label();
      OUTPUT("visitvar%d:", x);
      OUTPUT("movl $%d, %%eax", s->get_offset() + 4);
      OUTPUT("subl %%ebp, %%eax");
      OUTPUT("neg %%eax");
      OUTPUT("pushl %%eax");
    }

    void visitDerefVariable(DerefVariable* p)
    {
      DEBUG("visitDerefVariable");

      Symbol* s = m_st->lookup(p->m_attribute.m_scope, p->m_symname->spelling());

      DEBUG("%d", m_st->lexical_distance( s->get_scope(), p->m_attribute.m_scope ));

      // OUTPUT("addl $-%d, %%ebp", s->get_offset()+4);
      // OUTPUT("pushl %%ebp");
      // OUTPUT("addl $%d, %%ebp", s->get_offset()+4);
      OUTPUT("pushl -%d(%%ebp)", s->get_offset() + 4);
    }

    void visitArrayElement(ArrayElement* p)
    {
      DEBUG("visitArrayElement");
      //default_rule(p);
      p->m_symname->accept(this);
      p->m_expr->accept(this);
      Symbol *s=m_st->lookup(p->m_attribute.m_scope, p->m_symname->spelling());
      // OUTPUT("movl %%ebp, %%ecx");
      // OUTPUT("pop %%eax");
      // OUTPUT("imul $4, %%eax");
      // OUTPUT("addl %%eax, %%ecx");
      // OUTPUT("addl $%d, %%ecx", s->get_offset()+4);
      // OUTPUT("pushl %%ecx");//pushl $%d(%%ecx)", s->get_offset()+4);
    //  OUTPUT("label2:");
      OUTPUT("pop %%eax");
      //OUTPUT("imull $4, %%eax"); // Char's are 1 byte!

      //OUTPUT("push %%eax");
      // OUTPUT("pop %%ebx");
      // OUTPUT("pop %%ecx");
      // OUTPUT("push %%ecx");
      // OUTPUT("push %%ebx");
      // OUTPUT("push %%ecx");
      OUTPUT("neg %%eax");
      OUTPUT("addl $%d, %%eax", s->get_offset() + 4 + s->m_string_size-4-1);
      OUTPUT("subl %%ebp, %%eax");
      OUTPUT("neg %%eax");
      OUTPUT("pushl %%eax");

//      OUTPUT("asdf:");
      // OUTPUT("popl %%eax\n");
      // OUTPUT("pushl %%eax"); // HEREAA
      // OUTPUT("imull $4, %%eax");
      // OUTPUT("addl %%ebp, %%eax");
      // OUTPUT("pushl -4(%%eax)");
      //OUTPUT("movl %%ebx, %%ebp");
    }

    // Special cases
    void visitSymName(SymName* p)
    {
      DEBUG("visitSymName");
    }

    void visitPrimitive(Primitive* p)
    {
      DEBUG("visitPrimitive");
    }

    // Strings
    void visitStringAssignment(StringAssignment* p)
    {
      DEBUG("visitStringAssignment");
      //
      p->m_stringprimitive->accept(this);
      p->m_lhs->accept(this);
      //default_rule(p);

      DEBUG("SCOPE: %p", p->m_lhs->m_attribute.m_scope);
      //Symbol * s = m_st->lookup(p->m_lhs->m_attribute.m_scope,  "x");
      Symbol * s =m_st->lookup(p->m_lhs->m_attribute.m_scope, static_cast<Variable *>(p->m_lhs)->m_symname->spelling());
      //int i = -4 - s->get_offset();

      DEBUG("NAME: %s", static_cast<Variable *>(p->m_lhs)->m_symname->spelling());
      DEBUG("SYMBOL ADDRESS %p", s);
      DEBUG("OFFSET: %i", s->get_offset());
      DEBUG("SIZE: %u", s->m_string_size);
      uint i;
      for(i =0; i < s->m_string_size; i++ )
        if(p->m_stringprimitive->m_string[i] == 0)
          break;

      // Get string size
      int label = new_label();
      // OUTPUT("pop %%eax");
      // OUTPUT("label234:");
      // OUTPUT("cmp $0, %%eax");
      // OUTPUT("je label%d", label);
      // OUTPUT("pop %%ebx");
      //
      // OUTPUT("mov %%eax, %%ecx");
      // OUTPUT("imull $4, %%ecx");
      // OUTPUT("add $4, %%ecx");
      // OUTPUT("mov %%ebx, (%%ecx, %%ebp)");
      //
      // OUTPUT("add $-1, %%eax");
      // OUTPUT("jmp label234");
      // OUTPUT("label%d:", label);

      OUTPUT("pop %%ebx"); // address of variable
      //OUTPUT("pop %%ebx"); // Literally nothing :(
      //OUTPUT("LENGTH: %d", i);

      for(uint j = 0; j < i; j++){
        DEBUG("1");
        OUTPUT("\tpop %%eax");
        OUTPUT("\tmovb %%al, -%d(%%ebx)", j);
      }
    }

    void visitStringPrimitive(StringPrimitive* p)
    {
      DEBUG("visitStringPrimitive");
      int i = 0;
      while(p->m_string[i] != 0){
        DEBUG("STRING: %c", p->m_string[i]);
        OUTPUT("\tpush $%d", p->m_string[i++]);
      }
      //OUTPUT("\tpush $%d", i);
      OUTPUT("string%d:", new_label());
    }

    void visitAbsoluteValue(AbsoluteValue* p)
    {
      DEBUG("visitAbsoluteValue");
      default_rule(p);
      switch(p->m_expr->m_attribute.m_basetype){
        case bt_integer:
          OUTPUT("\tpopl %%eax");
          OUTPUT("\tmovl %%eax, %%ebx");
          OUTPUT("\tsarl $31, %%ebx");
          OUTPUT("\txorl %%ebx, %%eax");
          OUTPUT("\tsubl %%ebx, %%eax");
          OUTPUT("\tpushl %%eax");
        case bt_string:
          //OUTPUT("push $1");
        default: return;
      }
    }

    // Pointer
    void visitAddressOf(AddressOf* p)
    {
      DEBUG("visitAddressOf");
      default_rule(p);
      DEBUG("endvisitAddressof");
  //    Symbol * s =m_st->lookup(p->m_lhs->m_attribute.m_scope, static_cast<Variable *>(p->m_lhs)->m_symname->spelling());
      //OUTPUT("leal 4(%%eax), %%edi");
      //OUTPUT("lea %%eax, %%eax");
      //OUTPUT("push %%eax");

      OUTPUT("derk%d:", new_label());
      // OUTPUT("pop %%eax");
      // OUTPUT("pop %%ebx");
      //
      // OUTPUT("push %%ebx");
      // OUTPUT("push %%eax");
      //
      // OUTPUT("negl %%ebx");
      // OUTPUT("addl %%esp, %%ebx");
      // OUTPUT("pushl -%d(%%edx)", s->get_offset()+4);

      //OUTPUT("pushl -%d(%%esp)", s->get_offset()+4);
  //    OUTPUT("popl %%eax");
      //OUTPUT("addl $-%d, %%ebp", s->get_offset()+4)
//      OUTPUT("push -%d(%%eax)", s->get_offset()+4);

      //OUTPUT("addl $%d, %%ebp", s->get_offset()+4)
    }

    void visitDeref(Deref* p)
    {
      DEBUG("visitDeref");
      default_rule(p);
      OUTPUT("deref%d:", new_label());
      OUTPUT("popl %%eax");
      OUTPUT("movl (%%eax), %%eax");
      OUTPUT("and $255, %%eax");
      OUTPUT("push %%eax");
      //
      //OUTPUT("lea %%eax, %%eax");
      //OUTPUT("push %%eax");
      //OUTPUT("pushl 0(%%eax)");
    }
};


void dopass_codegen(Program_ptr ast, SymTab* st)
{
    Codegen* codegen = new Codegen(stdout, st);
    ast->accept(codegen);
    delete codegen;
}
