/*
 *  $Id: $
 *
 *  Copyright 2024 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 *  You need a C++0x compiler.
 *
 */

#ifndef INCLUDED_promela_generator_hpp_ae245f34_5c58_497a_ba9f_cb5cbbbb4151
#define INCLUDED_promela_generator_hpp_ae245f34_5c58_497a_ba9f_cb5cbbbb4151

#pragma once

#include "state_machine.hpp"

namespace upml {

/*
 *
 */
bool promela_generator(const upml::sm::state_machine& sm);

} //namespace upml


#endif //#define INCLUDED_promela_generator_hpp_ae245f34_5c58_497a_ba9f_cb5cbbbb4151
