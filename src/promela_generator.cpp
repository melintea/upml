/*
 *  $Id: $
 *
 *  Copyright 2024 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 *  You need a C++0x compiler.
 *
 */

#include "promela_generator.hpp"

namespace upml {

bool promela_generator(
    std::ostream&                  out,
    const upml::sm::state_machine& sm)
{
    out << '\n' << sm << '\n';
    return true;
}

} //namespace upml

