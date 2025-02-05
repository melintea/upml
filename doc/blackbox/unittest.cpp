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

    Switch sm1;
    sm1.start();
    assert(sm1._lightOn == false);
    
    std::cout << "> Send Event1" << std::endl;
    sm1.process_event(LampSwitch());
    assert(sm1._lightOn == false);

    sm1.process_event(WallSwitch());
    assert(sm1._lightOn == true);

    sm1.process_event(WallSwitch());
    assert(sm1._lightOn == false);
	
    return EXIT_SUCCESS;
}
