/*
 *  $Id: $
 *
 *  Copyright 2024 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 *  You need a C++0x compiler.
 *
 */

#define BOOST_SPIRIT_DEBUG      1
#define BOOST_SPIRIT_DEBUG_OUT  std::cerr
#define BOOST_SPIRIT_USE_PHOENIX_V3

#include "plantuml_parser.hpp"

#include <boost/phoenix/phoenix.hpp>
#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/support_line_pos_iterator.hpp>
#include <boost/fusion/include/adapt_struct.hpp>
#include <boost/fusion/include/io.hpp>

#include <string>
#include <iostream>

namespace bs = boost::spirit;
namespace bp = boost::phoenix;

// In the global scope
BOOST_FUSION_ADAPT_STRUCT(
    upml::sm::transition,
    (upml::sm::id_t, _id)
    (upml::sm::id_t, _fromState)
    (upml::sm::id_t, _toState)
    (upml::sm::id_t, _event)
    (upml::sm::id_t, _guard)
    (upml::sm::id_t, _effect)
)

BOOST_FUSION_ADAPT_STRUCT(
    upml::sm::region,
    (upml::sm::id_t, _id)
    (upml::sm::region::states_t, _substates)
)

BOOST_FUSION_ADAPT_STRUCT(
    upml::sm::state,
    (upml::sm::id_t, _id)
    (upml::sm::state::regions_t,     _regions)
    (upml::sm::state::transitions_t, _transitions)
)

BOOST_FUSION_ADAPT_STRUCT(
    upml::sm::state_machine,
    (upml::sm::id_t, _id)
    (upml::sm::state_machine::states_t, _substates)
)


namespace upml {

//namespace encoding = bs::qi::unicode;
namespace encoding = bs::qi::ascii;

template <typename It>
struct skipper final : bs::qi::grammar<It>
{
    skipper() : skipper::base_type(rule) {}

    const bs::qi::rule<It> rule = encoding::space 
            | ("#"  >> *~encoding::char_("\n")   >> -bs::qi::eol)
            | ("//" >> *~encoding::char_("\n")   >> -bs::qi::eol)
            | ("/*" >> *(encoding::char_ - "*/") >> "*/")
            ;
};

template <typename ITER, 
          typename SKIPPER
         >
struct plantuml_grammar final 
    : bs::qi::grammar<ITER, 
                      upml::sm::state_machine(), 
                      SKIPPER/*bs::ascii::space_type*/>
{
    plantuml_grammar() : plantuml_grammar::base_type(start)
    {
        qstring %= bs::qi::lexeme['"' >> +(bs::qi::char_ - '"') >> '"'];
        
        transition %= string >> bs::qi::lit("-->") >> string;

        //statements = transition;

        start = 
            bs::qi::lit("@startuml")
            //>> transition
            >> bs::qi::lit("@enduml")
            ;
        
        //BOOST_SPIRIT_DEBUG_NODES((start)(sm));
    }
    
    bs::qi::rule<ITER, std::string(), SKIPPER> qstring;
    bs::qi::rule<ITER, std::string(), SKIPPER> string;
    bs::qi::rule<ITER, upml::sm::transition(), SKIPPER>    transition;
    //bs::qi::rule<ITER, std::string(), SKIPPER> statements;
    bs::qi::rule<ITER, upml::sm::state_machine(), SKIPPER> start;
    
}; // plantuml_grammar

bool plantuml_parser(
    std::istream&            in,
    upml::sm::state_machine& sm)
{
    using base_iter_t        = bs::istream_iterator;
    using in_iter_t          = bs::line_pos_iterator<base_iter_t>; // base_iter_t; // 
    using skipper_t          = skipper<in_iter_t>; //
    using plantuml_grammar_t = plantuml_grammar<in_iter_t, 
                                                skipper_t 
                                               >;
    
    in_iter_t crtIt(base_iter_t(in >> std::noskipws));
    in_iter_t firstIt(crtIt);
    in_iter_t endIt;
    
    plantuml_grammar_t grammar;

    skipper_t skip = {};    
    bool match = bs::qi::phrase_parse(
                     crtIt, 
                     endIt, 
                     grammar,
                     skip, //bs::ascii::space,
                     sm);
    //std::cout << std::boolalpha << match << '\n';
    if ( ! match || crtIt != endIt)
    {
        std::cerr << "Parsing stopped at line " 
                  << bs::get_line(crtIt) << ':' << bs::get_column(firstIt, crtIt) << '\n' 
                  << '\'' << std::string{crtIt, endIt} << "'\n";
    }

    return match;
}

} //namespace upml

