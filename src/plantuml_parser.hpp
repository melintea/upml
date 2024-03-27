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
{
    ast_node* _parent{nullptr};
};
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
template <typename UPML_T> 
struct ast_visitor : boost::static_visitor<>
{
    mutable int _depth = 0;
    UPML_T& _target;

    ast_visitor(UPML_T& target, int depth = 0)
        : _target(target)
        , _depth(depth)
    {
        //boost::apply_visitor(*this, ast);
    }

    std::string tab() const
    {
        return std::string(2 * _depth, ' ');
    }

    template <typename T> 
    void operator()(T&) const
    {
        std::cout << tab() << "error" << std::endl;
    }

    void operator()(ast_null& n) const
    {
        std::cout << tab() << "ast_null line " << n._line << std::endl;
    }

    void operator()(ast_transition& n) const
    {
        std::cout << tab() << "ast_transition line " << n._line << std::endl;
        _target._id   = upml::sm::tag(_target._tag, _target._line);
    }

    void operator()(ast_state& n) const
    {
        std::cout << tab() << "ast_state line " << n._line << std::endl;
        //recurse<ast_state>(n);
    }

    void operator()(ast_region& n) const
    {
        std::cout << tab() << "ast_region line " << n._line << std::endl;
        _target._line = n._line;
        _target._col  = n._col;
        _target._file = n._file;
        _target._id   = upml::sm::tag(_target._tag, _target._line);
        //recurse<ast_region>(n);
    }

    void operator()(ast_machine& n) const
    {
        std::cout << "ast_machine line " << n._line << std::endl;
        _target._line = n._line;
        _target._col  = n._col;
        _target._file = n._file;
        _target._id   = upml::sm::tag(_target._tag, _target._line);

        ast_nodes_t& nodes = n._subtree;
        for (ast_node& subn : nodes)
        {
            upml::sm::region r;
            boost::apply_visitor(ast_visitor<upml::sm::region>(r, _depth+1), subn);
            _target._regions[r._id] = r;
        }
    }
}; // ast_visitor

template <>
inline void ast_visitor<upml::sm::region>::operator()(ast_machine& n) const {}

/*
 *
 */
bool plantuml_parser(
    std::istream&            in,
    upml::sm::state_machine& sm);

} //namespace upml


#endif //#define INCLUDED_plantuml_parser_hpp_f567faf6_5b3d_46ce_b12a_9552ec944049
