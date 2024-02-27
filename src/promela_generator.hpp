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

namespace lpt {

/*
 *
 */
class promela_generator
{
public:

    promela_generator()  {}
    ~promela_generator() {}

    promela_generator( const promela_generator& other );
    promela_generator& operator=( const promela_generator& other );

    promela_generator( const promela_generator& other );
    promela_generator& operator=( promela_generator&& other );
}; // promela_generator

} //namespace lpt


#endif //#define INCLUDED_promela_generator_hpp_ae245f34_5c58_497a_ba9f_cb5cbbbb4151
