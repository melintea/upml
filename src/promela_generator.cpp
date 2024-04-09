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

#include <chrono>

namespace upml {

bool promela_generator(
    std::ostream&                  out,
    const upml::sm::state_machine& sm)
{
    const auto now(std::chrono::system_clock::now());
    const auto nt(std::chrono::system_clock::to_time_t(now));

    out << "/*\n   Generated by UPML v" << UPML_VERSION << '\n'
        << "   at " << std::ctime(&nt)
        ;
    out << "\n\n" << sm << "\n*/\n\n\n";

    out << "init {skip}\n";
    
    return true;
}

} //namespace upml

