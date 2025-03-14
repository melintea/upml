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

// no recursive wrapper/heap allocation for std::variant, must use boost's
#include <boost/fusion/include/adapted.hpp>
#include <boost/variant.hpp>
#include <boost/variant/recursive_wrapper.hpp>

#include <iostream>
#include <source_location>


#ifdef ENABLE_UPML_DEBUG
#  define AST_DEBUG(x)  x
#else
#  define AST_DEBUG(x)  
#endif // ENABLE_UPML_DEBUG

// In the global scope
struct ast_null;
struct ast_transition;
struct ast_activity;
struct ast_config_setting;
struct ast_state;
struct ast_region;
struct ast_machine;

using ast_node =  boost::variant<
    ast_null,
    ast_transition, 
    ast_activity, 
    ast_config_setting,
    boost::recursive_wrapper<ast_state>, 
    boost::recursive_wrapper<ast_region>,
    ast_machine
>;
using ast_nodes_t = std::vector<ast_node>;

struct ast_node_base 
    : public upml::sm::location 
{
    //ast_node* _parent{nullptr};
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
    (upml::sm::transition::guard,  _guard)
    (upml::sm::transition::effect, _effect)
)

struct ast_activity 
    : public upml::sm::activity 
{};
BOOST_FUSION_ADAPT_STRUCT(
    ast_activity,
    //(upml::sm::id_t, _id)
    (upml::sm::id_t, _state)
    (upml::sm::id_t, _activity)
    (upml::sm::activity::args, _args)
)

struct ast_config_setting
    : public upml::sm::location
{
    upml::sm::id_t _state;
    std::string    _setting;
};
BOOST_FUSION_ADAPT_STRUCT(
    ast_config_setting,
    (upml::sm::id_t, _state)
    (std::string,    _setting)
)

struct ast_state 
    : public upml::sm::state
    //, public ast_nodes_t 
{
    upml::sm::id_t  _id;
    ast_nodes_t     _subtree;
};
BOOST_FUSION_ADAPT_STRUCT(
    ast_state,
    (upml::sm::id_t, _id)
    (ast_nodes_t,    _subtree)
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

    static sm::activity from_ast(const ast_activity& n)
    {
        sm::activity t;

        t._line      = n._line;
        t._col       = n._col;
        t._file      = n._file;

        t._id        = n._id;
        if (t._id.empty()) {
            t._id = sm::tag(sm::activity::_tag, n._line);
        }

        t._state     = n._state;
        t._activity  = n._activity;
        t._args      = n._args;  // TODO: move

        return t;
    }

    static sm::transition from_ast(const ast_transition& n)
    {
        sm::transition t;

        t._line      = n._line;
        t._col       = n._col;
        t._file      = n._file;

        t._id        = n._id;
        if (t._id.empty()) {
            t._id = sm::tag(sm::transition::_tag, n._line);
        }

        t._fromState = n._fromState;
        t._toState   = n._toState;
        t._event     = n._event;
        t._guard     = n._guard;
        t._effect    = n._effect;

        if (t._event.empty())
        {
            t._event = sm::tag(sm::event::_tag, t._line);
            std::cerr << "Warning: transition with unnamed event at line " 
                      << t._line << ": " << t._event << "\n";
        }

        return t;
    }

    template <typename NODE_T> 
    void annotate_target_from(NODE_T& n) const
    {
        this->_target._line = n._line;
        this->_target._col  = n._col;
        this->_target._file = n._file;
        this->_target._id   = n._id.empty() ? this->tag() : n._id;
    }

    void operator()(ast_activity& n) const
    {
        const auto loc(std::source_location::current());
        AST_DEBUG(std::cout << tab() << "bv error: " << loc.function_name() 
                            << " at line " << n._line
                            << std::endl;);
    }

    void operator()(ast_transition& n) const
    {
        const auto loc(std::source_location::current());
        AST_DEBUG(std::cout << tab() << "bv error: " << loc.function_name() 
                            << " at line " << n._line
                            << std::endl;);
    }

    void operator()(ast_config_setting& n) const
    {
        const auto loc(std::source_location::current());
        AST_DEBUG(std::cout << tab() << "bv error: " << loc.function_name() 
                            << " at line " << n._line
                            << std::endl;);
    }

    void operator()(ast_null& n) const
    {
        const auto loc(std::source_location::current());
        AST_DEBUG(std::cout << tab() << "bv error: " << loc.function_name() 
                            << " at line " << n._line
                            << std::endl;);
    }

    template <typename T> 
    void operator()(T& n) const
    {
        const auto loc(std::source_location::current());
        AST_DEBUG(std::cout << tab() << "bv error: " << loc.function_name() 
                            << " at line " << n._line
                            << std::endl;);
        ast_nodes_t& nodes = n._subtree;
        for (ast_node& subn : nodes)
        {
            boost::apply_visitor(*this, subn);
        }
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
        AST_DEBUG(std::cout << this->tab() << "v error: ast_null line " << n._line << std::endl;)
    }

    void operator()(ast_activity& n) const
    {
        AST_DEBUG(std::cout << this->tab() << "v ast_activity line " << n._line << std::endl;);
        this->annotate_target_from(n);
    }

    void operator()(ast_transition& n) const
    {
        AST_DEBUG(std::cout << this->tab() << "v ast_transition line " << n._line << std::endl;);
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

    void operator()(ast_state& n)           const;
    void operator()(ast_region& n)          const;

    upml::sm::regionptr_t new_region()      const;

}; // ast_visitor<upml::sm::state>

template <> 
struct ast_visitor<upml::sm::region> : public ast_base_visitor<upml::sm::region>
{
    ast_visitor(upml::sm::region& target, int depth = 0)
        : ast_base_visitor<upml::sm::region>(target, depth)
    {}

    using ast_base_visitor<upml::sm::region>::operator();

    void operator()(ast_state& n)            const;
    void operator()(ast_config_setting& n)   const;
    void operator()(ast_activity& n)         const;
    void operator()(ast_transition& n)       const;
    void operator()(ast_region& n)           const;
    
    upml::sm::stateptr_t state(const upml::sm::id_t& sid) const;
}; // ast_visitor<upml::sm::region>

template <> 
struct ast_visitor<upml::sm::state_machine> : public ast_base_visitor<upml::sm::state_machine>
{
    ast_visitor(upml::sm::state_machine& target, int depth = 0)
        : ast_base_visitor<upml::sm::state_machine>(target, depth)
    {}

    using ast_base_visitor<upml::sm::state_machine>::operator();

    void operator()(ast_region& n)  const;
    void operator()(ast_machine& n) const;
}; // ast_visitor<upml::sm::state_machine>

//-----------------------------------------------------------------------------

inline void ast_visitor<upml::sm::state>::operator()(ast_state& n) const
{
    AST_DEBUG(std::cout << this->tab() << "s ast_state line " << n._line << ": " << n._id << std::endl;);
    this->annotate_target_from(n);

    ast_nodes_t& nodes = n._subtree;
    for (ast_node& subn : nodes)
    {
        boost::apply_visitor(*this, subn);
    }
} // state

inline void ast_visitor<upml::sm::state>::operator()(ast_region& n) const
{
    AST_DEBUG(std::cout << this->tab() << "s ast_region line " << n._line << std::endl;)
    upml::sm::regionptr_t pr(new_region());
    ast_node v = n;
    boost::apply_visitor(upml::ast_visitor(*pr, this->_depth+1), v);
    this->_target._regions[pr->_id] = pr;
} // state                                                                                                                      
inline upml::sm::regionptr_t ast_visitor<upml::sm::state>::new_region() const
{
    upml::sm::regionptr_t pR(std::make_shared<upml::sm::region>());
    pR->_ownedByState = this->_target.shared_from_this();
    return pR;
} // state

//-----------------------------------------------------------------------------
inline upml::sm::stateptr_t ast_visitor<upml::sm::region>::state(const upml::sm::id_t& sid) const
{
    if (this->_target._ownedByState->_id == sid) {
        return this->_target._ownedByState;
    }
    
    auto it(this->_target._substates.find(sid));
    if (it != this->_target._substates.end()) {
        return it->second;
    }
    
    auto pState(std::make_shared<upml::sm::state>());
    pState->_ownedByRegion = this->_target.shared_from_this();
    pState->_superState    = this->_target._ownedByState;
    pState->_id = sid; 
    this->_target._substates[sid] = pState;
    return pState;
} // region

inline void ast_visitor<upml::sm::region>::operator()(ast_state& n) const
{
    AST_DEBUG(std::cout << this->tab() << "r ast_state line " << n._line << ": " << n._id << std::endl;);
    upml::sm::stateptr_t pst(state(n._id));
    ast_node v = n; // TODO: is this a deep copy?
    boost::apply_visitor(upml::ast_visitor(*pst, this->_depth+1), v);
} // region

inline void ast_visitor<upml::sm::region>::operator()(ast_config_setting& n) const
{
    AST_DEBUG(std::cout << this->tab() 
                << "r ast_config_setting line " << n._line 
                << ' ' << std::endl;);


    auto pState(state(n._state));
    pState->_config.insert(n._setting);
} // config_setting

inline void ast_visitor<upml::sm::region>::operator()(ast_activity& n) const
{
    auto tr(from_ast(n));
    AST_DEBUG(std::cout << this->tab() 
                << "r ast_activity line " << n._line 
                << ' ' << tr._id << std::endl;);

   
    auto pState(state(n._state));
    pState->_activities.push_back(tr);
} // region

inline void ast_visitor<upml::sm::region>::operator()(ast_transition& n) const
{
    auto tr(from_ast(n));
    AST_DEBUG(std::cout << this->tab() 
                << "r ast_transition line " << n._line 
                << ' ' << tr._id << std::endl;);

    bool init(n._fromState == "[*]");
    bool fin(n._toState == "[*]");

    if (init)
    {
        auto pState(state(n._toState));
        pState->_initial = true;
        return;
    }
    
    if (fin)
    {
        auto pState(state(n._fromState));
        pState->_final = true;
        return;
    }
    
    auto pFromState(state(n._fromState));
    pFromState->_transitions[tr._id] = tr;
    

    auto pToState(state(n._toState)); // force insertion if needed
} // region

inline void ast_visitor<upml::sm::region>::operator()(ast_region& n) const
{
    AST_DEBUG(std::cout << this->tab() << "r ast_region line " << n._line << std::endl;);
    this->annotate_target_from(n);

    ast_nodes_t& nodes = n._subtree;
    for (ast_node& subn : nodes)
    {
        boost::apply_visitor(*this, subn);
    }
} // region

inline void ast_visitor<upml::sm::state_machine>::operator()(ast_region& n) const
{
    AST_DEBUG(std::cout << this->tab() << "sm ast_region line " << n._line << std::endl;)
    
    upml::sm::regionptr_t pr(std::make_shared<upml::sm::region>());
    pr->_ownedByState = std::make_shared<upml::sm::state>(); // dummy owning state
    pr->_ownedByState->_id = this->_target._id; //upml::sm::tag('_', n._line);
    
    ast_node v = n;
    boost::apply_visitor(upml::ast_visitor(*pr, this->_depth+1), v);
    this->_target._regions[pr->_id] = pr;
} // state_machine

inline void ast_visitor<upml::sm::state_machine>::operator()(ast_machine& n) const
{
    AST_DEBUG(std::cout << "sm ast_machine line " << n._line << std::endl;);
    this->annotate_target_from(n);

    // TODO: automatically add a (default) region to every new state machine

    ast_nodes_t& nodes = n._subtree;
    for (ast_node& subn : nodes)
    {
        boost::apply_visitor(*this, subn);
    }
} // state_machine

//-----------------------------------------------------------------------------

/*
 *
 */
bool plantuml_parser(
    std::istream&            in,
    upml::sm::state_machine& sm);

} //namespace upml


#endif //#define INCLUDED_plantuml_parser_hpp_f567faf6_5b3d_46ce_b12a_9552ec944049
