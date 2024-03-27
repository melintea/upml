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

#include "state_machine.hpp"

// no recursive wrapper/heap allocation for std::variant
#include <boost/fusion/include/adapt_struct.hpp>
#include <boost/variant.hpp>
#include <boost/variant/recursive_wrapper.hpp>

#include <iostream>

// In the global scope
struct ast_null;
struct ast_transition;
struct ast_state;
struct ast_region;
struct ast_machine;

using ast_node =  boost::variant<
    ast_null,
    ast_transition, 
    boost::recursive_wrapper<ast_state>, 
    boost::recursive_wrapper<ast_region>,
    ast_machine
>;
using ast_nodes_t = std::vector<ast_node>;

struct ast_node_base 
    : public upml::sm::location 
{};
BOOST_FUSION_ADAPT_STRUCT(
    ast_node_base,
    (size_t,      _line)
    (size_t,      _col)
    (std::string, _file)
)

struct ast_null 
    : public upml::sm::location 
{};

struct ast_transition 
    : public upml::sm::transition 
{};
BOOST_FUSION_ADAPT_STRUCT(
    ast_transition,
    (upml::sm::id_t, _id)
    (upml::sm::id_t, _fromState)
    (upml::sm::id_t, _toState)
    (upml::sm::id_t, _event)
    (upml::sm::id_t, _guard)
    (upml::sm::id_t, _effect)
)


struct ast_state 
    : public upml::sm::state
    //, public ast_nodes_t 
{
    ast_nodes_t _subtree;
};
BOOST_FUSION_ADAPT_STRUCT(
    ast_state,
    (ast_nodes_t, _subtree)
)


struct ast_region 
    : public upml::sm::region
    //, public ast_nodes_t 
{
    ast_nodes_t _subtree;
};
BOOST_FUSION_ADAPT_STRUCT(
    ast_region,
    (ast_nodes_t, _subtree)
)


struct ast_machine 
    : public upml::sm::state_machine
    //, public ast_nodes_t 
{
    ast_nodes_t _subtree;
};
BOOST_FUSION_ADAPT_STRUCT(
    ast_machine,
    (ast_nodes_t, _subtree)
)


namespace upml {

/*
 *
 */
struct ast_visitor : boost::static_visitor<>
{
    int _depth = 0;
    upml::sm::state_machine& _sm;

    ast_visitor(const ast_node&          ast,
                upml::sm::state_machine& sm)
        : _sm(sm)
    {
        boost::apply_visitor(*this, ast);
    }

    std::string tab()
    {
        return std::string(2 * _depth, ' ');
    }

    void recurse(const ast_node& node)
    {
        ++_depth;
        boost::apply_visitor(*this, node);
        --_depth;
    }

    void recurse(const ast_nodes_t& nodes)
    {
        for (const ast_node& n : nodes)
        {
            recurse(n);
        }
    }

    void operator()(const ast_null& n)
    {
        std::cout << tab() << "ast_null line " << n._line << std::endl;
    }

    void operator()(const ast_transition& n)
    {
        std::cout << tab() << "ast_transition line " << n._line << std::endl;
        _sm._id   = upml::sm::tag(_sm._tag, _sm._line);
    }

    void operator()(const ast_state& n)
    {
        std::cout << tab() << "ast_state line " << n._line << std::endl;
        recurse(n._subtree);
    }

    void operator()(const ast_region& n)
    {
        std::cout << tab() << "ast_region line " << n._line << std::endl;
        recurse(n._subtree);
    }

    void operator()(const ast_machine& n)
    {
        std::cout << "ast_machine line " << n._line << std::endl;
        _sm._line = n._line;
        _sm._col  = n._col;
        _sm._file = n._file;
        _sm._id   = upml::sm::tag(_sm._tag, _sm._line);
        recurse(n._subtree);
    }

}; // ast_visitor

/*
 *
 */
bool plantuml_parser(
    std::istream&            in,
    upml::sm::state_machine& sm);

} //namespace upml


#endif //#define INCLUDED_plantuml_parser_hpp_f567faf6_5b3d_46ce_b12a_9552ec944049
