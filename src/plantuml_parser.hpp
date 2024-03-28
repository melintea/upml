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
#include <source_location>

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
    //(upml::sm::id_t, _id)
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
template <typename UPML_T> struct ast_visitor;

template <typename UPML_T> 
struct ast_base_visitor : public boost::static_visitor<>
{
    mutable int _depth = 0;
    UPML_T&     _target;

    ast_base_visitor(UPML_T& target, int depth = 0)
        : _depth(depth)
        , _target(target)
    {
        //boost::apply_visitor(*this, ast);
    }

    std::string tab() const
    {
        return std::string(2 * _depth, ' ');
    }

    std::string tag() const
    {
        return upml::sm::tag(this->_target._tag, this->_target._line);
    }

    template <typename NODE_T> 
    void annotate_target_from(NODE_T& n) const
    {
        this->_target._line = n._line;
        this->_target._col  = n._col;
        this->_target._file = n._file;
        this->_target._id   = this->tag();
    }

    template <typename T> 
    void operator()(T&) const
    {
        const auto loc(std::source_location::current());
        std::cout << tab() << "bv error: " << loc.function_name() << std::endl;
    }

}; // ast_base_visitor

template <typename UPML_T> 
struct ast_visitor : public ast_base_visitor<UPML_T>
{
    ast_visitor(UPML_T& target, int depth = 0)
        : ast_base_visitor<UPML_T>(target, depth)
    {}

    using ast_base_visitor<UPML_T>::operator();

    void operator()(ast_null& n) const
    {
        std::cout << this->tab() << "v error: ast_null line " << n._line << std::endl;
    }

    void operator()(ast_transition& n) const
    {
        std::cout << this->tab() << "v ast_transition line " << n._line << std::endl;
        this->annotate_target_from(n);
    }

}; // ast_visitor

template <> struct ast_visitor<upml::sm::state_machine>;
template <> struct ast_visitor<upml::sm::region>;
template <> struct ast_visitor<upml::sm::state>;
//template <> 
//struct ast_visitor<upml::sm::transition>;

template <> 
struct ast_visitor<upml::sm::state> : public ast_base_visitor<upml::sm::state>
{
    ast_visitor(upml::sm::state& target, int depth = 0)
        : ast_base_visitor<upml::sm::state>(target, depth)
    {}

    using ast_base_visitor<upml::sm::state>::operator();

    void operator()(ast_state& n) const
    {
        std::cout << this->tab() << "s ast_state line " << n._line << std::endl;
        this->annotate_target_from(n);
    }
}; // ast_visitor<upml::sm::state>

template <> 
struct ast_visitor<upml::sm::region> : public ast_base_visitor<upml::sm::region>
{
    ast_visitor(upml::sm::region& target, int depth = 0)
        : ast_base_visitor<upml::sm::region>(target, depth)
    {}

    using ast_base_visitor<upml::sm::region>::operator();

    void operator()(ast_transition& n) const
    {
        std::cout << this->tab() << "r ast_transition line " << n._line << std::endl;

        upml::sm::state from, to;
        from._id = n._fromState; 
        to._id   = n._toState;
        this->_target._substates[from._id] = std::make_shared<upml::sm::state>(from);
        this->_target._substates[to._id]   = std::make_shared<upml::sm::state>(to);
    }

    void operator()(ast_region& n) const
    {
        std::cout << this->tab() << "r ast_region line " << n._line << std::endl;
        this->annotate_target_from(n);

        ast_nodes_t& nodes = n._subtree;
        for (ast_node& subn : nodes)
        {
            boost::apply_visitor(*this, subn);
        }
    }
}; // ast_visitor<upml::sm::region>

template <> 
struct ast_visitor<upml::sm::state_machine> : public ast_base_visitor<upml::sm::state_machine>
{
    ast_visitor(upml::sm::state_machine& target, int depth = 0)
        : ast_base_visitor<upml::sm::state_machine>(target, depth)
    {}

    using ast_base_visitor<upml::sm::state_machine>::operator();

    void operator()(ast_region& n) const
    {
        std::cout << this->tab() << "sm ast_region line " << n._line << std::endl;
        upml::sm::region r;
        ast_node v = n;
        boost::apply_visitor(upml::ast_visitor(r, this->_depth+1), v);
        this->_target._regions[r._id] = r;
    }

    void operator()(ast_machine& n) const
    {
        std::cout << "sm ast_machine line " << n._line << std::endl;
        this->annotate_target_from(n);

        ast_nodes_t& nodes = n._subtree;
        for (ast_node& subn : nodes)
        {
            boost::apply_visitor(*this, subn);
        }
    }
}; // ast_visitor<upml::sm::state_machine>


/*
 *
 */
bool plantuml_parser(
    std::istream&            in,
    upml::sm::state_machine& sm);

} //namespace upml


#endif //#define INCLUDED_plantuml_parser_hpp_f567faf6_5b3d_46ce_b12a_9552ec944049
