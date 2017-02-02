#ifndef PRIMITIVE_HPP
#define PRIMITIVE_HPP

#include "ast.hpp"
#include "attribute.hpp"

class Primitive
{
  public:
  int m_data;
  Attribute* m_parent_attribute;

  Primitive(const Primitive &);

  Primitive &operator=(const Primitive &);
  Primitive(int x);
  ~Primitive();
  virtual void accept(Visitor *v);
  virtual Primitive *clone() const;
  void swap(Primitive &);
};


class StringPrimitive
{
  public:
  char *m_string;
  Attribute* m_parent_attribute;

  StringPrimitive(const StringPrimitive &);

  StringPrimitive &operator=(const StringPrimitive &);
  StringPrimitive(char *x);
  ~StringPrimitive();
  virtual void accept(Visitor *v);
  virtual StringPrimitive *clone() const;
  void swap(StringPrimitive &);
};




#endif //PRIMITIVE_HPP
