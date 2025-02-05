/*
 *  $Id: $
 *
 *  Copyright 2025 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 */

#ifndef INCLUDED_bindings_hpp_bcd69499_b890_4d28_a64a_9d681e53a49f
#define INCLUDED_bindings_hpp_bcd69499_b890_4d28_a64a_9d681e53a49f

#pragma once

extern "C" {

void initialize();
void terminate();

bool is_light_on();

void flip_wall_switch(); // WallSwitch
void flip_lamp_switch(); // LampSwitch

} //extern

#endif //#define INCLUDED_bindings_hpp_bcd69499_b890_4d28_a64a_9d681e53a49f
