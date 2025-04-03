/*
 *  $Id: $
 *
 *  Copyright 2024 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 *  You need a C++0x compiler.
 *
 */

#define BOOST_SPIRIT_DEBUG_OUT  std::cerr
#define BOOST_SPIRIT_USE_PHOENIX_V3

#include "plantuml_parser.hpp"
#include "keyword.hpp"
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

namespace qi       = bs::qi;
//namespace encoding = qi::unicode;
namespace encoding = qi::ascii;

// Escaped chars
struct _morphs : qi::symbols<const char, const char>
{
    _morphs() 
    {
        add
        ("\\;",  upml::keyword::stmtSep)
        ;
    }
} morphs; 

template <typename It>
struct skipper final : qi::grammar<It>
{
    skipper() : skipper::base_type(rule) {}

    const qi::rule<It> rule = encoding::space 
            | ("//" >> *~encoding::char_("\n")   >> -qi::eol)
            | ("/*" >> *(encoding::char_ - "*/") >> "*/")
            // --- legit plantuml not needed
            | ("hide empty description")
            | ("note" >> *(encoding::char_ - "end note") >> "end note")
            | ("note" >> *(encoding::char_ - ":") >> ":" >> *~encoding::char_("\n") >> -qi::eol)
            | ("skinparam" >> *~encoding::char_("\n")   >> -qi::eol)
            | ("skinparam state" >> *(encoding::char_ - "}") >> "}")
            | ("<style>" >> *(encoding::char_ - "</style>") >> "</style>")
            //| ("state" >> *encoding::char_("a-zA-Z0-9_") >> " as"  >> *~encoding::char_("\n") >> -qi::eol)
            // state "long state name" as ignored
            //| ("state \"" >> *~encoding::char_("\"") >> "\" as"  >> *(encoding::char_ - "{\n") >> -qi::eol)
            // state alias4 as "long name"
            //| ("json" >> *(encoding::char_ - "}") >> "}")
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
    using result_type = qi::error_handler_result;

    template<typename T1, typename T2, typename T3, typename T4>
    qi::error_handler_result operator()(T1 b, T2 e, T3 where, const T4& what) const 
    {
        auto dist(std::distance(b, where));
        std::cerr 
            << "Error: expecting " << what << " in line " << bs::get_line(where) << ":" << dist << ": \n"
            //<< std::string(b,e) << "\n"
            //<< std::setw(dist) << '^' << "---- here\n"
            ;
        return qi::fail;
    }
};


template <typename ITER, 
          typename SKIPPER
         >
struct plantuml_grammar final 
    : qi::grammar<ITER, 
                  ast_machine(), 
                  qi::locals<std::string>,
                  SKIPPER/*bs::ascii::space_type*/>
{
    plantuml_grammar(ITER first) 
        : plantuml_grammar::base_type(start)
        , locate(first)
    {
        using qi::on_error;
        using qi::on_success;
        using qi::fail;
        using qi::omit;
        using qi::eps;  // to init rule's result if needed
        using qi::_val; // rule's result
        using namespace qi::labels; // _a, ...

        arrow    %= qi::lit('-') >> *(qi::char_ - '-') >> qi::lit("->");
        
        qstring  %= qi::lexeme['"' >> +(qi::char_ - '"') >> '"'];
        rstring  %= qi::raw [ qi::lexeme[ +qi::char_("a-zA-Z0-9_.") ] ]
                 |  qi::string("[*]")
                 ;
        // conditions/checks expressions
        // [guard] & LTL expression                    ':' for scoped ids e.g. event:xxx
        tokexpr    %= qi::raw [ qi::lexeme[ +qi::char_("a-zA-Z0-9_.:") ] ]
                   |  qi::string("(")   |  qi::string(")")
                   |  qi::string("==")  |  qi::string("!=")
                   |  qi::string("&&")  |  qi::string("||")
                   |  qi::string("@")  // label
                   // LTL Promela syntax 
                   |  qi::string("{")   |  qi::string("}")
                   |  qi::string("!") 
                   |  qi::string("[]")  |  qi::string("<>")
                   |  qi::string("\\/") |  qi::string("/\\")
                   |  qi::string("->")  |  qi::string("<->")
                   ;

        // instructions/change-allowing expressions
        tokinstr   %= tokexpr
                   |  qi::string("=")
                   |  qi::string("[")   |  qi::string("]")
                   |  qi::lexeme[+morphs] // qi::as_string[morphs]
                   ;

        //discard = qi::lit("state") >> qstring >> qi::string("as") >> *(qi::char_ - '{')
        //        ;

        state = qi::lit("state") 
                    >  -qi::omit[qstring]             // long name
                    >> -qi::omit[qi::string("as")]
                    >> rstring
                    >> -qi::omit[*(qi::char_ - '{')]  // optional color
                    >> qi::lit("{")
                    >> regions 
                    >> qi::lit("}")
              ;
        // entry,exit, pre/postcondition,invariant, ltl
        //            _state    :     _activity   :      args
        activity %= rstring >> ':' >> rstring >> ':' >> *(tokinstr) > ';';

        //                _state:           config:                     _setting
        config_setting %= rstring >> ':' >> qi::lit(keyword::config) > ':' >> rstring > ';';

        //            _fromState  -->               _toState      :       _event        [     _guard          ]         /   _effect
        //transition %= rstring >> qi::omit[arrow] >> rstring >> -(':' >> rstring) >> -('[' >> *(rstring) > ']') >> -('/' >> *(rstring));
        transition %= rstring >> qi::omit[arrow] >> rstring >> -(':' >> -rstring) >> -('[' >> +(tokexpr) > ']') >> -('/' >> +(tokinstr) > ';');

        // There is one known limitation though, when you try to use a struct that has a single element that is also a container compilation fails unless you add qi::eps >> ... to your rule
        // https://stackoverflow.com/questions/78241220/boostspirit-error-no-type-named-value-type-in-struct-xxx
        region %= eps > +(config_setting | activity | transition | state)
               ;

        regions %= region/*default region*/ 
                >> *((qi::lit("--") | qi::lit("||")) >> region)
                ;

        start =  eps // error trigger point
              >  qi::lit("@startuml")
              >> regions 
              >> qi::lit("@enduml")
              ;

        on_success(activity,       locate(_val, _1, _3));
        on_success(transition,     locate(_val, _1, _3));
        on_success(config_setting, locate(_val, _1, _3));
        on_success(state,          locate(_val, _1, _3));
        on_success(region,         locate(_val, _1, _3));
        on_success(start,          locate(_val, _1, _3));

        // _3: errPosIt, _2: endIt, _1: rule enter pos
        on_error<fail>(start,          errorout(_1, _2, _3, _4));
        on_error<fail>(region,         errorout(_1, _2, _3, _4));
        on_error<fail>(state,          errorout(_1, _2, _3, _4));
        on_error<fail>(activity,       errorout(_1, _2, _3, _4));
        on_error<fail>(transition,     errorout(_1, _2, _3, _4));
        on_error<fail>(config_setting, errorout(_1, _2, _3, _4));
        
        BOOST_SPIRIT_DEBUG_NODES(
            (start)
            (regions)
            (region)
            (activity)
            (transition)
            (config_setting)
        );
    }

    bp::function<on_success_handler<ITER>> locate;
    bp::function<on_error_handler>         errorout;
    
    //qi::rule<ITER>   discard;
    qi::rule<ITER, std::string()> arrow;
    qi::rule<ITER, std::string()> qstring;   // "in quotes"
    qi::rule<ITER, std::string()> rstring;   // name string
    qi::rule<ITER, std::string()> tokexpr;   // expression tokens
    qi::rule<ITER, std::string()> tokinstr;  // instruction/activity/effect tokens
    qi::rule<ITER, ast_activity(), SKIPPER>        activity;
    qi::rule<ITER, ast_transition(), SKIPPER>      transition;
    qi::rule<ITER, ast_config_setting(), SKIPPER>  config_setting;
    qi::rule<ITER, ast_state(), SKIPPER>           state;
    qi::rule<ITER, ast_region(), SKIPPER>          region;
    qi::rule<ITER, ast_nodes_t(), SKIPPER>         regions;
    qi::rule<ITER, ast_machine(), qi::locals<std::string>, SKIPPER> start;
    
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

    ast_node ast;

    skipper_t skip = {};    
    bool match = qi::phrase_parse(
                     crtIt, 
                     endIt, 
                     grammar,
                     skip, //bs::ascii::space,
                     ast);
    //std::cout << std::boolalpha << match << '\n';
    
    if ( ! match || crtIt != endIt)
    {
        std::cerr << "Parsing stopped at line " 
                  << bs::get_line(crtIt) << ':' << bs::get_column(firstIt, crtIt) 
                  << " pos " << std::distance(firstIt, crtIt) << '\n' 
                  //<< '\'' << std::string{crtIt, endIt} << "'\n"
                  ;
        return false;
    }
    /*
    if ( ! match )
    {
        return false;
    }
    */

    upml::ast_visitor prn(sm);
    boost::apply_visitor(prn, ast);

    return true;
}

} //namespace upml

