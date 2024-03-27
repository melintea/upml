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
#include "state_machine.hpp"

#include <boost/phoenix/phoenix.hpp>
#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/support_line_pos_iterator.hpp>
#include <boost/fusion/include/io.hpp>

#include <string>
#include <iomanip>
#include <iostream>

namespace bs = boost::spirit;
namespace bp = boost::phoenix;


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

template <typename It> 
auto lines(const It& b, const It& e)
{
    return std::count_if(b, e, [](char ch){return ch == '\n'; });
}

template <typename It> 
struct on_success_handler 
{
    using result_type = void;

    const It   _first;

    on_success_handler(It first) : _first(first) {}

    template <typename Val, typename First, typename Last>
    void operator()(Val& v, First f, Last l) const
    {
        store_location(v, f, l, _first);
        //v._id = upml::sm::tag(v._tag, v._line);
    }

    static void store_location(upml::sm::location& loc, It f, It l, It first)
    {
        loc._line = bs::get_line(f);
        loc._col  = bs::get_column(first, f);
        //std::cerr << " [" << loc << "]\n";
    }
    static void store_location(...) { std::cerr << "(not location-derived)\n"; }
};

struct on_error_handler 
{
    using result_type = bs::qi::error_handler_result;

    template<typename T1, typename T2, typename T3, typename T4>
    bs::qi::error_handler_result operator()(T1 b, T2 e, T3 where, const T4& what) const 
    {
        std::cerr 
            << "Error: expecting " << what << " in line " << bs::get_line(where) << ": \n"
            //<< std::string(b,e) << "\n"
            //<< std::setw(std::distance(b, where)) << '^' << "---- here\n"
            ;
        return bs::qi::fail;
    }
};


template <typename ITER, 
          typename SKIPPER
         >
struct plantuml_grammar final 
    : bs::qi::grammar<ITER, 
                      ast_machine(), 
                      bs::qi::locals<std::string>,
                      SKIPPER/*bs::ascii::space_type*/>
{
    plantuml_grammar(ITER first) 
        : plantuml_grammar::base_type(start)
        , locate(first)
    {
        using bs::qi::on_error;
        using bs::qi::fail;
        using bs::qi::eps;  // init rule's result if needed
        using bs::qi::_val; // rule's result
        using namespace bs::qi::labels; // _a, ...

        qstring  %= bs::qi::lexeme['"' >> +(bs::qi::char_ - '"') >> '"'];
        rstring  %= bs::qi::raw [ bs::qi::lexeme[ +bs::qi::char_("a-zA-Z0-9_") ] ] ;
        
        transition %= rstring >> bs::qi::lit("-->") >> rstring;

        // There is one known limitation though, when you try to use a struct that has a single element that is also a container compilation fails unless you add qi::eps >> ... to your rule
	    // https://stackoverflow.com/questions/50252680/boost-spirit-x3-parser-no-type-named-type-in
        region %= eps >> transition
               ;

        regions %= eps >> *region
                ;

        start = eps >
            bs::qi::lit("@startuml") //[ bp::push_back(bp::ref(_val._subtree), ast_region()) ]
            >> regions
            >> bs::qi::lit("@enduml")
            ;

        on_success(transition, locate(_val, _1, _3));
        on_success(region,     locate(_val, _1, _3));
        on_success(start,      locate(_val, _1, _3));

        // _3: errPosIt, _2: endIt, _1: rule enter pos
        on_error<fail>(start,      errorout(_1, _2, _3, _4));
        on_error<fail>(region,     errorout(_1, _2, _3, _4));
        on_error<fail>(transition, errorout(_1, _2, _3, _4));
        
        BOOST_SPIRIT_DEBUG_NODES(
            (start)
            (regions)
            (region)
            (transition)
        );
    }

    bp::function<on_success_handler<ITER>> locate;
    bp::function<on_error_handler>         errorout;
    
    bs::qi::rule<ITER, std::string(), SKIPPER> qstring;
    bs::qi::rule<ITER, std::string(), SKIPPER> rstring;
    bs::qi::rule<ITER, ast_transition(), SKIPPER>    transition;
    bs::qi::rule<ITER, ast_region(), SKIPPER>    region;
    bs::qi::rule<ITER, ast_nodes_t(), SKIPPER>    regions;
    bs::qi::rule<ITER, ast_machine(), bs::qi::locals<std::string>, SKIPPER> start;
    
}; // plantuml_grammar

bool plantuml_parser(
    std::istream&            in,
    upml::sm::state_machine& sm)
{
    using base_iter_t        = bs::istream_iterator;
    using lp_iter_t          = bs::line_pos_iterator<base_iter_t>;
    using in_iter_t          = lp_iter_t;  // base_iter_t; // 
    using skipper_t          = skipper<in_iter_t>; //
    using plantuml_grammar_t = plantuml_grammar<in_iter_t, 
                                                skipper_t 
                                               >;
    
    in_iter_t crtIt(base_iter_t(in >> std::noskipws));
    in_iter_t firstIt(crtIt);
    in_iter_t endIt;
    
    plantuml_grammar_t grammar(firstIt);

    ast_machine ast;

    skipper_t skip = {};    
    bool match = bs::qi::phrase_parse(
                     crtIt, 
                     endIt, 
                     grammar,
                     skip, //bs::ascii::space,
                     ast);
    //std::cout << std::boolalpha << match << '\n';
    /*
    if ( ! match || crtIt != endIt)
    {
        std::cerr << "Parsing stopped at line " 
                  << bs::get_line(crtIt) << ':' << bs::get_column(firstIt, crtIt) << '\n' 
                  << '\'' << std::string{crtIt, endIt} << "'\n";
    }
    */

    if ( ! match )
    {
        return false;
    }

    ast_visitor prn(ast, sm);

    return true;
}

} //namespace upml

