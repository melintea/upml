/*
 *  $Id: $
 *
 *  Copyright 2024 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 *  You need a C++0x compiler.
 *
 */

#ifndef INCLUDED_indent_hpp_e8f6f9cd_cde2_4ab8_b0f0_9d0ce3ad485f
#define INCLUDED_indent_hpp_e8f6f9cd_cde2_4ab8_b0f0_9d0ce3ad485f

#pragma once

#include <iostream>
#include <string>

namespace upml {

/*
 * Trace helper.
 */
struct indent
{
    std::string _indent;

    indent() : _indent{"    "} {}
    indent(std::string s) : _indent{std::move(s)} {}

    ~indent()                        = default;
    indent(const indent&)            = default;
    indent& operator=(const indent&) = default;
    indent(indent&&)                 = default;
    indent& operator=(indent&&)      = default;

    indent& operator++()     { _indent += "    "; return *this;}
    indent  operator++(int)          = delete;
    indent& operator--()     { _indent.resize(_indent.size() -4); return *this;}
    indent  operator--(int)          = delete;

    friend std::ostream& operator<<(std::ostream& os, const indent& i);
}; // indent

inline std::ostream& operator<<(std::ostream& os, const indent& i)
{
    os << i._indent;
    return os;
}

struct indent_scope
{
    indent& _indent;

    indent_scope(indent& i) : _indent{i} { ++_indent; }
    ~indent_scope() { --_indent; }

    indent_scope(const indent_scope&)            = delete;
    indent_scope& operator=(const indent_scope&) = delete;
    indent_scope(indent_scope&&)                 = delete;
    indent_scope& operator=(indent_scope&&)      = delete;

    friend std::ostream& operator<<(std::ostream& os, const indent_scope& i);
};

inline std::ostream& operator<<(std::ostream& os, const indent_scope& i)
{
    os << i._indent;
    return os;
}

} //namespace upml


#endif //#define INCLUDED_indent_hpp_e8f6f9cd_cde2_4ab8_b0f0_9d0ce3ad485f
