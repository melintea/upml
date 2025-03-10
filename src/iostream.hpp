/*
 *  $Id: $
 *
 *  Copyright 2024 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 *  You need a C++0x compiler.
 *
 */

#ifndef INCLUDED_iostream_hpp_16afdfdb_5c40_473f_9d2c_5fd3cf8fb6f6
#define INCLUDED_iostream_hpp_16afdfdb_5c40_473f_9d2c_5fd3cf8fb6f6

#pragma once


#include <cassert>
#include <string>
#include <iostream>


/**
 * iostream tools
 */

namespace lpt {

/** Poor performance indenting ostream
 *  @see also https://stackoverflow.com/questions/1391746/how-to-easily-indent-output-to-ofstream
 *  for better ideas
 *
 *  Usage:
 *
 *    std::ostream& operator<<(std::ostream& os, const l1& x)
 *    {
 *        lpt::autoindent_guard indent(os);
 *        os << "(l1\n" << ... << ")l1";
 *        return os;
 *    }
 *
 *    lpt::autoindent_ostream ios(std::cout);
 *    ios << l1() << std::endl;
 */

struct autoindent_ostream : private std::streambuf
                          , public std::ostream
{
    autoindent_ostream(std::ostream& os) 
        : std::ostream(this) 
    , _os(os)
    {}

    autoindent_ostream()   = delete;
    ~autoindent_ostream()  = default;

    autoindent_ostream( const autoindent_ostream& other )            = default;
    autoindent_ostream& operator=( const autoindent_ostream& other ) = default;

    autoindent_ostream( autoindent_ostream&& other )                 = default;
    autoindent_ostream& operator=( autoindent_ostream&& other )      = default;
    
    int level(int delta)
    {
        int crt(_level);
    
        _level += delta;
        if (_level < 0) {
            _level = 0;
        }
    
        return crt;
    }
    
    void reset(int level)
    {
        assert(level >= 0);
        _level = level;
    }
    
    void indent()
    {
        _os << sc_indent;
    }

private:

    int overflow(int c) override
    {
        _os.put(c);
        if (c == '\n') {
            for (int i = 0; i <_level; ++i) {
                indent();
            }
        }
    
        return 0;
    }

    std::ostream& _os;
    int           _level{0};
    
    static constexpr const char* sc_indent = "    ";

}; // autoindent_ostream


class autoindent_guard
{
public:

    autoindent_guard(std::ostream& ios, int delta = 1)
        : _ios(ios)
    {
        auto pOs(dynamic_cast<autoindent_ostream*>(&_ios));
        if (pOs) {
            _oldlevel = pOs->level(delta);
            pOs->indent();
        }
    }
    
    autoindent_guard()   = delete;
    
    ~autoindent_guard()
    {
        auto pOs(dynamic_cast<autoindent_ostream*>(&_ios));
        if (pOs) {
            pOs->reset(_oldlevel);
        }
    }

    autoindent_guard( const autoindent_guard& other )            = delete;
    autoindent_guard& operator=( const autoindent_guard& other ) = delete;

    autoindent_guard( autoindent_guard&& other )                 = delete;
    autoindent_guard& operator=( autoindent_guard&& other )      = delete;
    
    
private:
    
    std::ostream&  _ios;
    int            _oldlevel{0};

}; // autoindent_guard

} //namespace lpt


#endif //#define INCLUDED_iostream_hpp_16afdfdb_5c40_473f_9d2c_5fd3cf8fb6f6
