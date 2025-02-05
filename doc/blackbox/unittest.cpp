/*
 *  $Id: $
 *
 *  Copyright 2025 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 */

#include "bindings.hpp"

#include <cassert>
#include <cstdlib>
#include <iostream>

int main()
{
    initialize();
    assert(is_light_on() == false);
    
    std::cout << "> Send Event1" << std::endl;
    flip_lamp_switch();
    assert(is_light_on() == false);

    flip_wall_switch();
    assert(is_light_on() == true);

    flip_wall_switch();
    assert(is_light_on() == false);
	
    return EXIT_SUCCESS;
}
