#ifndef ATTRIBUTE_HPP
#define ATTRIBUTE_HPP

#include <cstddef>

// SymScope is declared in SymTab.cpp
class SymScope;

enum Basetype
{
    bt_undef,

    bt_integer,
    bt_intptr,
    bt_boolean,
    bt_char,
    bt_charptr,
    bt_procedure,
    bt_ptr,             // Used by nullptr
    bt_string
};


class Attribute
{
  public:
  Basetype m_basetype;  // Type of the subtree
  int m_place;          // Register where this value is stored
  SymScope* m_scope;    // The scope of the current symbol
  int lineno;           // Line number on which that ast node resides

  Attribute() {
    m_basetype = bt_undef;
    lineno = 0;
    m_scope = NULL;
    int m_place = -1;   // Should never actually be negative
  }
};

#endif //ATTRIBUTE_HPP

