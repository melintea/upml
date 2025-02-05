/*
 *  $Id: $
 *
 *  Copyright 2025 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 */

#include "bindings.hpp"
#include "switch_state_machine.hpp"

#include <iostream>


Switch g_sm;


void initialize()
{
    g_sm.start();
}

void terminate()
{
}

bool is_light_on()
{
    return g_sm._lightOn;
}

void flip_wall_switch()
{
    std::cout << "WallSwitch\n";
    g_sm.process_event(WallSwitch());
}

void flip_lamp_switch()
{
    std::cout << "LampSwitch\n";
    g_sm.process_event(LampSwitch());
}
