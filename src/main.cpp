/*
 *  $Id: $
 *
 *  Copyright 2024 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 *  You need a C++0x compiler.
 *
 */

#include "plantuml_parser.hpp"
#include "promela_generator.hpp"

#include <cstdlib>
#include <iostream>
#include <fstream>

int main(int argc, char* argv[])
{
    upml::sm::state_machine sm;
    
    //std::fstream in("../plantuml/t0.plantuml"); 
    bool ret =  upml::plantuml_parser(std::cin, //in, //std::cin, 
                                      sm)
             && upml::promela_generator(sm)
	     ;
    
    return ret ? EXIT_SUCCESS : EXIT_FAILURE;
}

