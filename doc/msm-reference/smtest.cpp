/*
 *  $Id: $
 *
 *  Copyright 2025 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 */

#include "sm1.hpp"

#include <cassert>
#include <cstdlib>
#include <iostream>

int main()
{

    {
        sm1::SM sm1;
        sm1.start();
    
        sm1.process_event(sm1::T4());
        sm1.process_event(sm1::T1());
        sm1.process_event(sm1::T4());
        sm1.process_event(sm1::T5());
        sm1.process_event(sm1::T2());
        sm1.process_event(sm1::T3());
    }
    
    return EXIT_SUCCESS;
}
