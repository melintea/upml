/*
 *  $Id: $
 *
 *  Copyright 2024 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 *  You need a C++0x compiler.
 *
 */

#ifndef INCLUDED_pluscal_generator_hpp_e94097d6_5656_4154_821b_c92761e084cb
#define INCLUDED_pluscal_generator_hpp_e94097d6_5656_4154_821b_c92761e084cb

#pragma once

#include "state_machine.hpp"

namespace upml::tla {

namespace hsm {

/*
 * HSM
 */
bool generate(
    std::ostream&            out,
    upml::sm::state_machine& sm);

} // hsm

namespace fsm {

/*
 * FSM model
 */
bool generate(
    std::ostream&            out,
    upml::sm::state_machine& sm);

} // fsm

} //namespace upml::tla


#endif //#define INCLUDED_pluscal_generator_hpp_e94097d6_5656_4154_821b_c92761e084cb
