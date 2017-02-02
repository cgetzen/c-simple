#include <algorithm>
#include <string.h>
#include "primitive.hpp"

/*************/
/* Primitive */
/*************/

Primitive::~Primitive()
{
}

Primitive::Primitive(int x)
{
    m_data = x;
    m_parent_attribute = NULL;
}

Primitive::Primitive(const Primitive & other)
{
    m_data = other.m_data;
    m_parent_attribute = other.m_parent_attribute;
}

Primitive& Primitive::operator=(const Primitive & other)
{
    Primitive tmp(other);
    swap(tmp);
    return *this;
}

void Primitive::accept(Visitor *v)
{
    v->visitPrimitive(this);
}

Primitive* Primitive::clone() const
{
    return new Primitive(*this);
}

void Primitive::swap(Primitive & other)
{
    std::swap(m_data, other.m_data);
}


/*******************/
/* StringPrimitive */
/*******************/

StringPrimitive::StringPrimitive(char *x)
{
    m_string = x;
    m_parent_attribute = NULL;
}

StringPrimitive::StringPrimitive(const StringPrimitive & other)
{
    m_string = strdup(other.m_string);
    m_parent_attribute = other.m_parent_attribute;
}

StringPrimitive::~StringPrimitive()
{
    delete (m_string);
}

StringPrimitive& StringPrimitive::operator=(const StringPrimitive & other)
{
    delete m_string;
    StringPrimitive tmp(other);
    swap(tmp);
    return *this;
}

void StringPrimitive::accept(Visitor *v)
{
    v->visitStringPrimitive(this);
}

StringPrimitive* StringPrimitive::clone() const
{
    return new StringPrimitive(*this);
}

void StringPrimitive::swap(StringPrimitive & other)
{
    std::swap(m_string, other.m_string);
}
