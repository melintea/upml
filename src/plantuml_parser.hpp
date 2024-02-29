/*
 *  $Id: $
 *
 *  Copyright 2024 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 *  You need a C++0x compiler.
 *
 */

#ifndef INCLUDED_plantuml_parser_hpp_f567faf6_5b3d_46ce_b12a_9552ec944049
#define INCLUDED_plantuml_parser_hpp_f567faf6_5b3d_46ce_b12a_9552ec944049

#pragma once

#include "state_machine.hpp"

#include <iostream>

namespace upml {

/*
 *
 */
bool plantuml_parser(
    std::istream&            in,
    upml::sm::state_machine& sm);

} //namespace upml


#endif //#define INCLUDED_plantuml_parser_hpp_f567faf6_5b3d_46ce_b12a_9552ec944049
