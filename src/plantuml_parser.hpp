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

namespace lpt {

/*
 *
 */
class plantuml_parser
{
public:

    plantuml_parser()  {}
    ~plantuml_parser() {}

    plantuml_parser( const plantuml_parser& other );
    plantuml_parser& operator=( const plantuml_parser& other );

    plantuml_parser( const plantuml_parser& other );
    plantuml_parser& operator=( plantuml_parser&& other );
}; // plantuml_parser

} //namespace lpt


#endif //#define INCLUDED_plantuml_parser_hpp_f567faf6_5b3d_46ce_b12a_9552ec944049
