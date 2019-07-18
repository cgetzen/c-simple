#include <iostream>
#include <cstdio>
#include <cstring>

#include "ast.hpp"
#include "symtab.hpp"
#include "primitive.hpp"
#include "assert.h"

#define MAINSTR string("Main")
#define DEBUG(x) //do { cout << x << endl; } while (0)

using namespace std;

#define default_rule(X)  X->m_attribute.m_scope = m_st->get_scope(); \
      X->visit_children(this);

#include <typeinfo>

class Typecheck : public Visitor {
  private: 
    FILE* m_errorfile;
    SymTab* m_st;

    // The set of recognized errors
    enum errortype
    {
        no_main,            // check_for_one_main()
        nonvoid_main,
        dup_proc_name,      // add_proc_symbol()
        dup_var_name,       // add_decl_symbol()
        proc_undef,
        call_type_mismatch,
        narg_mismatch,
         expr_type_err,
        var_undef,          // check_call()
        ifpred_err,         // check_pred_if()
        whilepred_err,      // check_pred_while()
        incompat_assign,    // check_call() check_assignment()
        who_knows,
        ret_type_mismatch,  // check_proc()
        array_index_error,
        no_array_var,       // check_return()
        arg_type_mismatch,
        expr_pointer_arithmetic_err,
        expr_abs_error,
        expr_addressof_error,
        invalid_deref
    };

    // Print the error to file and exit
    void t_error(errortype e, Attribute a) {
        fprintf(m_errorfile,"on line number %d, ", a.lineno);

        switch(e) {
            case no_main:
                fprintf(m_errorfile, "error: no main\n");
                exit(2);
            case nonvoid_main:
                fprintf(m_errorfile, "error: the Main procedure has arguments\n");
                exit(3);
            case dup_proc_name:
                fprintf(m_errorfile, "error: duplicate procedure names in same scope\n");
                exit(4);
            case dup_var_name:
                fprintf(m_errorfile, "error: duplicate variable names in same scope\n");
                exit(5);
            case proc_undef:
                fprintf(m_errorfile, "error: call to undefined procedure\n");
                exit(6);
            case var_undef:
                fprintf(m_errorfile, "error: undefined variable\n");
                exit(7);
            case narg_mismatch:
                fprintf(m_errorfile, "error: procedure call has different number of args than declartion\n");
                exit(8);
            case arg_type_mismatch:
                fprintf(m_errorfile, "error: argument type mismatch\n");
                exit(9);
            case ret_type_mismatch:
                fprintf(m_errorfile, "error: type mismatch in return statement\n");
                exit(10);
            case call_type_mismatch:
                fprintf(m_errorfile, "error: type mismatch in procedure call args\n");
                exit(11);
            case ifpred_err:
                fprintf(m_errorfile, "error: predicate of if statement is not boolean\n");
                exit(12);
            case whilepred_err:
                fprintf(m_errorfile, "error: predicate of while statement is not boolean\n");
                exit(13);
            case array_index_error:
                fprintf(m_errorfile, "error: array index not integer\n");
                exit(14);
            case no_array_var:
                fprintf(m_errorfile, "error: attempt to index non-array variable\n");
                exit(15);
            case incompat_assign:
                fprintf(m_errorfile, "error: type of expr and var do not match in assignment\n");
                exit(16);
            case expr_type_err:
                fprintf(m_errorfile, "error: incompatible types used in expression\n");
                exit(17);
            case expr_abs_error:
                fprintf(m_errorfile, "error: absolute value can only be applied to integers and strings\n");
                exit(17);
            case expr_pointer_arithmetic_err:
                fprintf(m_errorfile, "error: invalid pointer arithmetic\n");
                exit(18);
            case expr_addressof_error:
                fprintf(m_errorfile, "error: AddressOf can only be applied to integers, chars, and indexed strings\n");
                exit(19);
            case invalid_deref:
                fprintf(m_errorfile, "error: Deref can only be applied to integer pointers and char pointers\n");
                exit(20);
            default:
                fprintf(m_errorfile, "error: no good reason\n");
                exit(21);
        }
    }

    // Helpers
    std::vector<Basetype> push_back_args(std::list<Decl_ptr> * s) {
      std::vector<Basetype> * b = new std::vector<Basetype>;
      for (auto iter = s->begin(); iter != s->end(); ++iter){
          int size = static_cast<DeclImpl *>(*iter)->m_symname_list->size();
          while(size-->0)
              b->push_back(static_cast<DeclImpl *>(*iter)->m_type->m_attribute.m_basetype);
      }
      return *b;
    }

    bool OnlyOneMain(list<Proc_ptr>::iterator begin, list<Proc_ptr>::iterator end){
      bool found = false;
      for(; begin != end; ++begin){
        string name = static_cast<ProcImpl *>(*begin)->m_symname->spelling();
        DEBUG(name);

        if(name == MAINSTR) found = true;
        std::list<Proc_ptr> *recurse=static_cast<Procedure_blockImpl *>(static_cast<ProcImpl *>(*begin)->m_procedure_block)->m_proc_list;

        if( OnlyOneMain(recurse->begin(), recurse->end()) )
            this->t_error(no_main, (*begin)->m_attribute);
      }
      return found;
    }


    // Type Checking

    // Check that there is one and only one main
    void check_for_one_main(ProgramImpl* p) {
      DEBUG("Check for one main");
      list<Proc_ptr> * iter = p->m_proc_list;
      OnlyOneMain(iter->begin(), iter->end());

       bool found = false;
       for(auto iter = p->m_proc_list->begin(); iter != p->m_proc_list->end(); ++iter) {
         string name = static_cast<ProcImpl *>(*iter)->m_symname->spelling();
         if(name == MAINSTR && found == true)
           this->t_error(no_main,  p->m_attribute);
         if(name == MAINSTR)
           found = true;
       }
       if(! found)
         this->t_error(no_main,  p->m_attribute);
    }

    // Create a symbol for the procedure and check there is none already
    // existing

    void add_proc_symbol(ProcImpl* p) {
      DEBUG("Add proc symbol");

      // To allow recursion!
      p->m_type->accept(this);
      for(auto i = p->m_decl_list->begin(); i != p->m_decl_list->end(); ++i)
        static_cast<DeclImpl *>(*i)->m_type->accept(this);


      char * name = strdup(p->m_symname->spelling());
      Symbol *s = new Symbol();

      s->m_basetype = bt_procedure;
      s->m_arg_type = push_back_args(p->m_decl_list);
      s->m_return_type = p->m_type->m_attribute.m_basetype;

      DEBUG(name);

      if(m_st->exist(name)){
        if(name == MAINSTR){
          DEBUG("1234");
          this->t_error(no_main, p->m_attribute);
        }
        // Allow nested functions to have the same name :(
        //this->t_error(dup_proc_name, p->m_attribute);
      }

      if(!m_st->insert(name,s)){
        this->t_error(dup_proc_name, p->m_attribute);
      }
      if(MAINSTR == name) {
        // Ensure Main returns integer
        // if(p->m_type->m_attribute.m_basetype != bt_integer)
        //   this->t_error(ret_type_mismatch, p->m_type->m_attribute);
        if(s->m_arg_type.size() > 0)
          this->t_error(nonvoid_main, p->m_attribute);
      }
    }

    // Add symbol table information for all the declarations following
    void add_decl_symbol(DeclImpl* p) {
      char * name;
      Symbol *s;

      for(auto iter = p->m_symname_list->begin(); iter != p->m_symname_list->end(); iter++){
        name = strdup ((*iter)->spelling());
        s = new Symbol();
        s->m_basetype = p->m_type->m_attribute.m_basetype;
        if(s->m_basetype == bt_string) s->m_string_size = ((TString *)p->m_type)->m_primitive->m_data+4;

        DEBUG("Adding symbol: "); DEBUG(name);
        // Don't look in upper scopes :(
        if (/*m_st->exist(name) ||*/ ! m_st->insert(name, s))
          this->t_error(dup_var_name,  p->m_attribute);
        DEBUG(m_st->lookup(name)->m_basetype);
        DEBUG(s->get_scope());
        DEBUG("IMPORTANT");
      }

    }

    // Check that the return statement of a procedure has the appropriate type
    void check_proc(ProcImpl *p) {
      // DEBUG << p->m_type->m_parent_attribute->m_basetype << endl;
      // DEBUG << p->m_type->m_attribute.m_basetype << endl;
      // DEBUG << static_cast<Procedure_blockImpl *>(p->m_procedure_block)->m_return_stat->m_attribute.m_basetype << endl;
      // Type* == Basetype
      DEBUG(p->m_type->m_attribute.m_basetype);
      DEBUG(static_cast<Procedure_blockImpl *>(p->m_procedure_block)->m_return_stat->m_attribute.m_basetype);
      if(p->m_type->m_attribute.m_basetype != static_cast<Procedure_blockImpl *>(p->m_procedure_block)->m_return_stat->m_attribute.m_basetype)
        this->t_error(ret_type_mismatch, p->m_attribute);

    }

    // Check that the declared return type is not an array
    void check_return(Return *p) {
      switch (p->m_attribute.m_basetype) {
        case bt_string:
          this->t_error(dup_proc_name,  p->m_attribute);
        default: ;
        }
    }

    // Create a symbol for the procedure and check there is none already
    // existing
    void check_call(Call *p) {
      //DEBUG << "Check Call: " << p->m_symname->spelling() << m_st->lookup(p->m_symname->spelling())->m_basetype << endl;
      Symbol *s = m_st->lookup(p->m_symname->spelling());

      // Is Symbol defined and a function?
      if(! s || s->m_basetype != bt_procedure)
        this->t_error(proc_undef,  p->m_attribute);

      DEBUG(p->m_expr_list->size());DEBUG(s->m_arg_type.size());
      // Do the number of parameters match?
      if( p->m_expr_list->size() != s->m_arg_type.size() )
        this->t_error(narg_mismatch,  p->m_attribute);
      DEBUG("here");
      // Do the types of parameters match?
      auto call_iter = p->m_expr_list->begin();
      auto symb_iter = s->m_arg_type.begin();
      for(int i = 0, size = p->m_expr_list->size(); i < size; i++){
        DEBUG((*(call_iter))->m_attribute.m_basetype);DEBUG(*(symb_iter + i));
        if( (*(call_iter++))->m_attribute.m_basetype != *(symb_iter + i) )
          this->t_error(arg_type_mismatch,  p->m_attribute);
      }

      // Does the Lhs match the return type
      if( p->m_lhs->m_attribute.m_basetype != m_st->lookup(p->m_symname->spelling())->m_return_type)
        this->t_error(call_type_mismatch, p->m_attribute);

    }

    // For checking that this expressions type is boolean used in if/else
    void check_pred_if(Expr* p) {
      if(p->m_attribute.m_basetype != bt_boolean)
        this->t_error(ifpred_err, p->m_attribute);
    }

    // For checking that this expressions type is boolean used in while
    void check_pred_while(Expr* p) {
      if(p->m_attribute.m_basetype != bt_boolean)
        this->t_error(whilepred_err, p->m_attribute);
    }

    void check_assignment(Assignment* p) {
      DEBUG("Check_assignment");
      if(p->m_expr->m_attribute.m_basetype == bt_ptr &&
        (p->m_lhs->m_attribute.m_basetype == bt_charptr || p->m_lhs->m_attribute.m_basetype == bt_intptr))
        return;
      if(p->m_lhs->m_attribute.m_basetype != p->m_expr->m_attribute.m_basetype)
        this->t_error(incompat_assign, p->m_attribute);

    }


    // For checking boolean operations(and, or ...)
    void checkset_boolexpr(Expr* parent, Expr* child1, Expr* child2) {
      if(parent->m_attribute.m_basetype != bt_boolean ||
         child1->m_attribute.m_basetype != bt_boolean ||
         child2->m_attribute.m_basetype != bt_boolean)
        this->t_error(expr_type_err,  parent->m_attribute);
    }

    // For checking arithmetic expressions(plus, times, ...)
    void checkset_arithexpr(Expr* parent, Expr* child1, Expr* child2) {
      if(child1->m_attribute.m_basetype == bt_charptr ||
         child1->m_attribute.m_basetype == bt_intptr ||
         child2->m_attribute.m_basetype == bt_charptr ||
         child2->m_attribute.m_basetype == bt_intptr)
        this->t_error(expr_pointer_arithmetic_err,  parent->m_attribute);

      if(parent->m_attribute.m_basetype != bt_integer ||
         child1->m_attribute.m_basetype != bt_integer ||
         child2->m_attribute.m_basetype != bt_integer)
        this->t_error(expr_type_err,  parent->m_attribute);
    }

    // Called by plus and minus: in these cases we allow pointer arithmetics
    void checkset_arithexpr_or_pointer(Expr* parent, Expr* child1, Expr* child2) {
      if(parent->m_attribute.m_basetype != bt_charptr ||
         child1->m_attribute.m_basetype != bt_charptr ||
         child2->m_attribute.m_basetype != bt_integer)
        this->t_error(expr_pointer_arithmetic_err,  parent->m_attribute);
    }

    // For checking relational(less than , greater than, ...)
    void checkset_relationalexpr(Expr* parent, Expr* child1, Expr* child2) {
      if(parent->m_attribute.m_basetype != bt_boolean ||
         child1->m_attribute.m_basetype != bt_integer ||
         child2->m_attribute.m_basetype != bt_integer)
        this->t_error(expr_type_err,  parent->m_attribute);
    }

    // For checking equality ops(equal, not equal)
    void checkset_equalityexpr(Expr* parent, Expr* child1, Expr* child2) {
      if(parent->m_attribute.m_basetype != bt_boolean)
        this->t_error(expr_type_err,  parent->m_attribute);

      if(child1->m_attribute.m_basetype == bt_string)
        this->t_error(expr_type_err,  parent->m_attribute);

      if(child1->m_attribute.m_basetype != child2->m_attribute.m_basetype){
        if(child1->m_attribute.m_basetype == bt_ptr &&
           (child2->m_attribute.m_basetype == bt_charptr || child2->m_attribute.m_basetype == bt_intptr))
          return;
        if(child2->m_attribute.m_basetype == bt_ptr &&
           (child1->m_attribute.m_basetype == bt_charptr || child1->m_attribute.m_basetype == bt_intptr))
          return;
        this->t_error(expr_type_err,  parent->m_attribute);
      }
    }

    // For checking not
    void checkset_not(Expr* parent, Expr* child) {
      if(child->m_attribute.m_basetype != bt_boolean ||
         parent->m_attribute.m_basetype != bt_boolean)
        this->t_error(expr_type_err,  parent->m_attribute);
    }

    // For checking unary minus
    void checkset_uminus(Expr* parent, Expr* child) {
      if(child->m_attribute.m_basetype != bt_integer ||
         parent->m_attribute.m_basetype != bt_integer)
        this->t_error(expr_type_err,  parent->m_attribute);
    }

    void checkset_absolute_value(Expr* parent, Expr* child) {
      if(parent->m_attribute.m_basetype != bt_integer ||
         (child->m_attribute.m_basetype != bt_integer && child->m_attribute.m_basetype != bt_string))
        this->t_error(expr_abs_error,  parent->m_attribute);
    }



  public:

    Typecheck(FILE* errorfile, SymTab* st) {
        m_errorfile = errorfile;
        m_st = st;
    }

    void visitProgramImpl(ProgramImpl* p) {
      DEBUG("visitProgramImpl");
      default_rule(p);
      check_for_one_main(p);
      m_st->dump(stderr);
    }

    void visitProcImpl(ProcImpl* p) {
      DEBUG("visitProcImpl");

      add_proc_symbol(p);

      m_st->open_scope();
      default_rule(p);
      m_st->close_scope();

      check_proc(p);

    }

    void visitCall(Call* p) {
      DEBUG("visitCall: ");
      default_rule(p);

      check_call(p);
    }

    void visitNested_blockImpl(Nested_blockImpl* p) {
      DEBUG("visitNested_blockImpl");
      m_st->open_scope();
      default_rule(p);
      m_st->close_scope();
    }

    void visitProcedure_blockImpl(Procedure_blockImpl* p) {
      DEBUG("visitProcedure_blockImpl");
      default_rule(p);


    }

    void visitDeclImpl(DeclImpl* p) {
      DEBUG("visitDeclImpl");
      default_rule(p);

      add_decl_symbol(p);
    }

    void visitAssignment(Assignment* p) {
      DEBUG("visitAssignment");
      default_rule(p);

      Basetype lhs = p->m_lhs->m_attribute.m_basetype;
      Basetype expr= p->m_expr->m_attribute.m_basetype;

      if(lhs != expr){
        if((expr == bt_undef || expr == bt_ptr) && (lhs == bt_intptr || lhs == bt_charptr))
          return;
        DEBUG(lhs);
        DEBUG(expr);
        this->t_error(incompat_assign,  p->m_attribute);
      }
    }

    void visitStringAssignment(StringAssignment *p) {
      DEBUG("visitStringAssignment");
      default_rule(p);
      if(m_st->lookup(static_cast<Variable *>(p->m_lhs)->m_symname->spelling())->m_string_size < string(p->m_stringprimitive->m_string).length()){
        this->t_error(array_index_error,  p->m_attribute);
      }
    }

    void visitIdent(Ident* p) {
      DEBUG("visitIdent: ");
      default_rule(p);

      if(! m_st->lookup(p->m_symname->spelling()))
        this->t_error(var_undef,  p->m_attribute);
      p->m_attribute.m_basetype = m_st->lookup(p->m_symname->spelling())->m_basetype;
      p->m_parent_attribute->m_basetype = p->m_attribute.m_basetype;
      DEBUG( p->m_attribute.m_basetype);

    }

    void visitReturn(Return* p) {
      DEBUG("visitReturn");
      default_rule(p);
      p->m_attribute.m_basetype = p->m_expr->m_attribute.m_basetype;
    }

    void visitIfNoElse(IfNoElse* p) {
      DEBUG("visitIfNoElse");
      default_rule(p);

      if(p->m_expr->m_attribute.m_basetype != bt_boolean)
        this->t_error(ifpred_err,  p->m_attribute);
    }

    void visitIfWithElse(IfWithElse* p) {
      DEBUG("visitIfWithElse");
      default_rule(p);

      if(p->m_expr->m_attribute.m_basetype != bt_boolean)
        this->t_error(ifpred_err,  p->m_attribute);
    }

    void visitWhileLoop(WhileLoop* p) {
      DEBUG("visitWhileLoop");
      default_rule(p);

      if(p->m_expr->m_attribute.m_basetype != bt_boolean)
        this->t_error(whilepred_err,  p->m_attribute);
    }

    void visitCodeBlock(CodeBlock *p) {
      DEBUG("visitCodeBlock");
      default_rule(p);
    }

    void visitTInteger(TInteger* p) {
      DEBUG("visitTInteger: ");
      default_rule(p);
      p->m_attribute.m_basetype = bt_integer;
    }

    void visitTBoolean(TBoolean* p) {
      DEBUG("visitTBoolean");
      default_rule(p);
      p->m_attribute.m_basetype = bt_boolean;
    }

    void visitTCharacter(TCharacter* p) {
      DEBUG("visitTCharacter");
      default_rule(p);
      p->m_attribute.m_basetype = bt_char;
    }

    void visitTString(TString* p) {
      DEBUG("visitTString");
      default_rule(p);
      p->m_attribute.m_basetype = bt_string;
      //p->m_attribute.string_size = 1;
    }

    void visitTCharPtr(TCharPtr* p) {
      DEBUG("visitTCharPtr");
      default_rule(p);
      p->m_attribute.m_basetype = bt_charptr;
    }

    void visitTIntPtr(TIntPtr* p) {
      DEBUG("visitTIntPtr");
      default_rule(p);
      p->m_attribute.m_basetype = bt_intptr;
    }

    void visitAnd(And* p) {
      DEBUG("visitAnd");
      default_rule(p);
      p->m_attribute.m_basetype = bt_boolean;
      checkset_boolexpr(p, p->m_expr_2, p->m_expr_1);
    }

    void visitDiv(Div* p) {
      DEBUG("visitDiv");
      default_rule(p);
      p->m_attribute.m_basetype = bt_integer;
      checkset_arithexpr(p, p->m_expr_2, p->m_expr_1);

    }

    void visitCompare(Compare* p) {
      DEBUG("visitCompare");
      default_rule(p);
      p->m_attribute.m_basetype = bt_boolean;
      checkset_equalityexpr(p, p->m_expr_1, p->m_expr_2);
    }

    void visitGt(Gt* p) {
      DEBUG("visitGt");
      default_rule(p);
      p->m_attribute.m_basetype = bt_boolean;
      checkset_relationalexpr(p, p->m_expr_1, p->m_expr_2);
    }

    void visitGteq(Gteq* p) {
      DEBUG("visitGteq");
      default_rule(p);
      p->m_attribute.m_basetype = bt_boolean;
      checkset_relationalexpr(p, p->m_expr_1, p->m_expr_2);
    }

    void visitLt(Lt* p) {
      DEBUG("visitLt");
      default_rule(p);
      p->m_attribute.m_basetype = bt_boolean;
      checkset_arithexpr(p->m_expr_1, p->m_expr_2, p->m_expr_1);
    }

    void visitLteq(Lteq* p) {
      DEBUG("visitLteq");
      default_rule(p);
      p->m_attribute.m_basetype = bt_boolean;
      checkset_relationalexpr(p, p->m_expr_1, p->m_expr_2);
    }

    void visitMinus(Minus* p) {
      DEBUG("visitMinus");

      default_rule(p);

      switch(p->m_expr_1->m_attribute.m_basetype){
        case bt_charptr:
          p->m_attribute.m_basetype = bt_charptr;
          checkset_arithexpr_or_pointer(p, p->m_expr_1, p->m_expr_2);
          break;
        case bt_integer:
          p->m_attribute.m_basetype = bt_integer;
          checkset_arithexpr(p, p->m_expr_1, p->m_expr_2);
          break;
        case bt_intptr:
          this->t_error(expr_pointer_arithmetic_err,  p->m_attribute);
        default:
          this->t_error(expr_type_err,  p->m_attribute);
      }
    }

    void visitNoteq(Noteq* p) {
      DEBUG("visitNoteq");
      default_rule(p);
      p->m_attribute.m_basetype = bt_boolean;
      checkset_equalityexpr(p, p->m_expr_1, p->m_expr_2);
    }

    void visitOr(Or* p) {
      DEBUG("visitOr");
      default_rule(p);
      p->m_attribute.m_basetype = bt_boolean;
      checkset_boolexpr(p, p->m_expr_2, p->m_expr_1);
    }

    void visitPlus(Plus* p) {
      DEBUG("visitPlus");
      default_rule(p);


      switch(p->m_expr_1->m_attribute.m_basetype){
        case bt_charptr:
          p->m_attribute.m_basetype = bt_charptr;
          checkset_arithexpr_or_pointer(p, p->m_expr_1, p->m_expr_2);
          break;
        case bt_integer:
          p->m_attribute.m_basetype = bt_integer;
          checkset_arithexpr(p, p->m_expr_1, p->m_expr_2);
          break;
        case bt_intptr:
          this->t_error(expr_pointer_arithmetic_err,  p->m_attribute);
        default:
          this->t_error(expr_type_err,  p->m_attribute);
      }
    }

    void visitTimes(Times* p) {
      DEBUG("visitTimes");
      default_rule(p);
      p->m_attribute.m_basetype = bt_integer;
      checkset_arithexpr(p->m_expr_1, p->m_expr_2, p->m_expr_1);
    }

    void visitNot(Not* p) {
      DEBUG("visitNot");
      default_rule(p);
      p->m_attribute.m_basetype = bt_boolean;
      checkset_not(p, p->m_expr);
    }

    void visitUminus(Uminus* p) {
      DEBUG("visitUminus");
      default_rule(p);
      p->m_attribute.m_basetype = bt_integer;
      checkset_uminus(p, p->m_expr);

    }

    void visitArrayAccess(ArrayAccess* p) {
      DEBUG("visitArrayAccess");
      default_rule(p);
      p->m_attribute.m_basetype = bt_char;
      if(m_st->lookup(p->m_symname->spelling())->m_basetype != bt_string)
        this->t_error(no_array_var, p->m_attribute);

      if(p->m_expr->m_attribute.m_basetype != bt_integer) {
        this->t_error(array_index_error, p->m_attribute);
      }
    }

    void visitIntLit(IntLit* p) {
      DEBUG("visitIntLit");
      default_rule(p);
      p->m_attribute.m_basetype = bt_integer;
    }

    void visitCharLit(CharLit* p) {
      DEBUG("visitCharLit");
      default_rule(p);
      p->m_attribute.m_basetype = bt_char;
    }

    void visitBoolLit(BoolLit* p) {
      DEBUG("visitBoolLit");
      default_rule(p);
      p->m_attribute.m_basetype = bt_boolean;
    }

    void visitNullLit(NullLit* p) {
      DEBUG("visitNullLit");
      default_rule(p);
      p->m_attribute.m_basetype = bt_ptr;
    }

    void visitAbsoluteValue(AbsoluteValue* p) {
      DEBUG("visitAbsoluteValue");
      default_rule(p);
      p->m_attribute.m_basetype = bt_integer;
      checkset_absolute_value(p, p->m_expr);
    }

    void visitAddressOf(AddressOf* p) {
      DEBUG("visitAddressOf");
      default_rule(p);
      switch(p->m_lhs->m_attribute.m_basetype){
        case bt_integer:
          p->m_attribute.m_basetype = bt_intptr;
          return;
        case bt_char:
          p->m_attribute.m_basetype = bt_charptr;
          return;
        default:
          this->t_error(expr_addressof_error, p->m_attribute);
      }
    }

    void visitVariable(Variable* p) {
      DEBUG("visitVariable: " << p->m_symname->spelling());
      default_rule(p);
      if(! m_st->lookup(p->m_symname->spelling()))
        this->t_error(var_undef, p->m_attribute);
      p->m_attribute.m_basetype = m_st->lookup(p->m_symname->spelling())->m_basetype;
      DEBUG( p->m_attribute.m_basetype);
    }

    void visitDeref(Deref* p) {
      DEBUG("visitDeref");
      default_rule(p);
      switch(p->m_expr->m_attribute.m_basetype){
        case bt_intptr:
          p->m_attribute.m_basetype = bt_integer;
          return;
        case bt_charptr:
          p->m_attribute.m_basetype = bt_char;
          return;
        default:
          this->t_error(invalid_deref, p->m_attribute);
      }
    }

    void visitDerefVariable(DerefVariable* p) {
      DEBUG("visitDerefVariable");

      default_rule(p);

      switch(m_st->lookup(p->m_symname->spelling())->m_basetype){
        case bt_intptr:
          p->m_attribute.m_basetype = bt_integer;
          return;
        case bt_charptr:
          p->m_attribute.m_basetype = bt_char;
          return;
        default:
          this->t_error(invalid_deref, p->m_attribute);
      }
    }

    void visitArrayElement(ArrayElement* p) {
      DEBUG("visitArrayElement");
      default_rule(p);

      if(m_st->lookup(p->m_symname->spelling())->m_basetype != bt_string)
        this->t_error(no_array_var, p->m_attribute);

      if(p->m_expr->m_attribute.m_basetype != bt_integer) {
        this->t_error(array_index_error, p->m_attribute);
      }
      p->m_attribute.m_basetype = bt_char;
    }

    // Special cases
    void visitPrimitive(Primitive* p) {
      DEBUG("visitPrimitive");

    }
    void visitSymName(SymName* p) {
      DEBUG("visitSymName: ");DEBUG(p->spelling());

    }
    void visitStringPrimitive(StringPrimitive* p) {
      DEBUG("visitStringPrimitive");
      DEBUG(string(p->m_string).length()+1);
      //p->m_parent_attribute->m_basetype = 1;
    }
};


void dopass_typecheck(Program_ptr ast, SymTab* st)
{
    Typecheck* typecheck = new Typecheck(stderr, st);
    ast->accept(typecheck); // Walk the tree with the visitor above
    delete typecheck;
}
