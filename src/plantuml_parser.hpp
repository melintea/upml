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

// no recursive wrapper/heap allocation for std::variant
#include <boost/variant.hpp>
#include <boost/variant/recursive_wrapper.hpp>

#include <iostream>

namespace upml {

using value =  boost::variant<
    sm::transition,
    //sm::state, 
    //sm::region,
    boost::recursive_wrapper<sm::state>, 
    boost::recursive_wrapper<sm::region>,
    sm::state_machine
>;

/*
 *
 */
bool plantuml_parser(
    std::istream&            in,
    upml::sm::state_machine& sm);

} //namespace upml


#endif //#define INCLUDED_plantuml_parser_hpp_f567faf6_5b3d_46ce_b12a_9552ec944049
