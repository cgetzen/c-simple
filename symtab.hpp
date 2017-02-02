#ifndef SYMTAB_HPP
#define SYMTAB_HPP

#include <algorithm>
#include <functional>
#include <unordered_map>
#include <vector>
#include <ext/hash_map>

#include <cassert>

#include "ast.hpp"
#include "attribute.hpp"

class Symbol;

class SymName
{
  private:
    char* m_spelling; // "name" of the symbol
    Symbol* m_symbol; // Pointer to the symbol for this name

  public:
    SymName(const SymName &);
    SymName &operator=(const SymName &);
    SymName(char* const x);
    ~SymName();
    virtual void accept(Visitor *v);
    virtual SymName *clone() const;
    void swap(SymName &);

    const char* spelling();
    const char* mangled_spelling();
    Symbol* symbol();
    void set_symbol( Symbol* symbol );

    Attribute* m_parent_attribute; // pointer to the attribute of the parent of this node
};

// this is one-level of scope for the SymTab
// it is not defined in the hpp file because it
// is only used internally in the implementation of SymTab.
// Pointers to SymScope are used to point to an internal
// part of a SymTab and are returned by get_scope and
// queried with lookup.
class SymScope;

// this is where the symbol information is actually stored.
// details of the symbol including it's type, parameters, etc.
// can be kept in this class
class Symbol
{
  private:
    int m_offset;
    SymScope* m_symscope;

  public:
    // We don't need to store symbol name in the actual symbol
    // because we can get a copy of that from the symbol table

    // Valid for all types
    Basetype m_basetype;

    // These are valid only if they are procedures
    std::vector<Basetype> m_arg_type;
    Basetype m_return_type;

    //WRITEME: add string size information
    uint m_string_size;

    Symbol()
    {
        m_offset = -1;
        m_symscope = NULL;
        m_basetype = bt_undef;
        m_string_size = 0;
    }

    int get_size()
    {
      switch(m_basetype)
      {
        case bt_integer:
            return(4);
        case bt_boolean:
            return(4);
        case bt_char:
            return(4);
        case bt_procedure:
            return(0);
        case bt_string:
            if (m_string_size <= 0) assert(0);
            return(m_string_size);
        case bt_ptr:
            return(4);
        case bt_charptr:
            return(4);
        case bt_intptr:
            return(4);
        case bt_undef:
            // Fall through
        default:
            assert(0);

        // WRITEME: add string size calc and assert size != 0
      }
    }

    // If either of these assert fails, you tried to get a variable that was
    // not set (which means it was not inserted properly into the symbol
    // table)
    int get_offset()
    {
        assert(m_offset >= 0);
        return m_offset;
    }

    SymScope* get_scope()
    {
        assert(m_symscope != NULL);
        return m_symscope;
    }

    friend class SymScope;
    friend class SymTab;

    ~Symbol() { }
};

// This is the symbol table header which is similar to the interface described
// in class. There is a open and close scope to grow a symbol table tree.
// lookup and exist recurisively search all of the parent scopes, while insert
// considers only the current scope.  An example chunk of code is below
class SymTab
{
  private:
    SymScope* m_head;
    SymScope* m_cur_scope;
    bool is_dup_string(char*);

  public:
    SymTab();
    ~SymTab();

    void open_scope();
    void close_scope();

    // Return the current scope so that we can search within that scope later
    SymScope* get_scope();

    // Returns true if name is found in the current SymTab or any of the
    // parents
    bool exist(char* name);

    // Tries to insert a pointer to s into the symbol table and returns true
    // if successful.
    // name should be a "fresh" copy, meaning that the SymTab will keep track
    // of the memory pointed to by name and free it in the destructor. name
    // should not point to some memory that has already been inserted into the
    // symtab (see example)
    bool insert(char* name, Symbol* s);

    // Does an insert into the parent scope of the working scope (it will have
    // an assert failure if there is no parent scope)
    bool insert_in_parent_scope(char* name, Symbol* s);

    // Tries to locate name in the current SymTab and all of the parent
    // SymTabs
    Symbol* lookup(const char* name);

    // Tries to locate name in the specified target scope and all of the
    // parent scopes.
    Symbol* lookup(SymScope* targetscope, const char* name);

    // Returns the size of the targetscope (in bytes) in terms of the total
    // amount of space that would be required to store all the variables in
    // that scope.
    int scopesize(SymScope* targetscope);

    // Returns the lexical distantance between deeper_scope and higher_scope.
    // the lexical depth is the levels of nesting between the two (if there
    // are in the same nest then the distance is 0).  If deeper_scope is not
    // _nested_inside_ the higher_scope as assertion will fail
    int lexical_distance(SymScope* higher_scope, SymScope* deeper_scope);

    // Dump the contents of the symbol table to the file
    // descriptor provided.  very useful for debugging
    void dump(FILE* f);
};

#endif //SYMTAB_HPP

/*
* //---------------------------------------------
* // SymTab example code
* //---------------------------------------------
*   SymTab st;
*
*   // each entry in the SymTab needs a unique copy of
*   // a string for the key (which it will delete
*   // in the destructor)
*   char* foo_string = strdup("foo");
*   char* foo2_string = strdup("foo");
*   char* bar_string = strdup("bar");
*
*   // each entry also needs a pointer to a symbol.
*   // don't need to be uniqe, multiple
*   // enties might point to the same symbol
*   Symbol* foo_s = new Symbol();
*   Symbol* bar_s = new Symbol();
*
*   bool is_inserted;
*   is_inserted = st.insert( foo_string, foo_s );
*   assert( is_inserted );
*   is_inserted = st.insert( bar_string, bar_s );
*   assert( is_inserted );
*   is_inserted = st.insert( foo2_string, foo_s );
*   // this assert should fail if uncommented because
*   // the above insert would not have been successful
*   // because there is another "foo" in this scope
*   //assert( is_inserted );
*
*   st.open_scope();
*
*   // if you uncomment the statement below, it should
*   // fail because it is trying to put a second copy
*   // of the "foo" pointed to by foo_string.
*   // is_inserted = st.insert( foo_string, foo_s );
*
*   // instead you need to insert a differt string
*   // which has the same contents
*   is_inserted = st.insert( foo2_string, foo_s );
*   assert( is_inserted );
*
*   Symbol* f;
*   // now some lookups
*
*   // should find this in the current scope
*   f = st.lookup(foo2_string);
*   assert( f != NULL );
*   fprintf(stderr,"(%s)\n",f->spelling());
*   assert( !strcmp(f->spelling(),"foo") );
*
*   // should find this in the parent scope
*   f = st.lookup(bar_string);
*   assert( f != NULL);
*   fprintf(stderr,"(%s)\n",f->spelling());
*   assert( !strcmp(f->spelling(),"bar") );
*
*   // should not find this at all
*   f = st.lookup("snap");
*   assert( f == NULL);
* //--------------------------------------------
*/
