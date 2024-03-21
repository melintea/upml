/*
 *  $Id: $
 *
 *  Copyright 2024 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 *  You need a C++0x compiler.
 *
 */

#ifndef INCLUDED_state_machine_hpp_6ab84852_1aea_4eb0_8f3c_fd6054e765ea
#define INCLUDED_state_machine_hpp_6ab84852_1aea_4eb0_8f3c_fd6054e765ea

#pragma once

#include <algorithm>
#include <cassert>
#include <iostream>
#include <memory>
#include <string>
#include <map>  // unordered not supported by boost::spirit/phoenix?
#include <set>

namespace upml::sm {

inline std::string id(char c, int num)
{
    //return std::vformat("{}{}", std::make_format_args(c, num));
    return std::string(1, c) + std::to_string(num);
}

// Trace helper
struct indent
{
    std::string _indent;

    indent() : _indent{"    "} {}
    indent(std::string s) : _indent{std::move(s)} {}

    ~indent()                        = default;
    indent(const indent&)            = default;
    indent& operator=(const indent&) = default;
    indent(indent&&)                 = default;
    indent& operator=(indent&&)      = default;

    indent& operator++()     { _indent += "    "; return *this;}
    indent  operator++(int)          = delete;
    indent& operator--()     { _indent.resize(_indent.size() -4); return *this;}
    indent  operator--(int)          = delete;

    friend std::ostream& operator<<(std::ostream& os, const indent& i);
};

inline std::ostream& operator<<(std::ostream& os, const indent& i)
{
    os << i._indent;
    return os;
}


using id_t = std::string;

// helper
template <typename T> struct hasher
{
    size_t operator()(const T& s) const { return std::hash<id_t>()(s._id); }
    size_t operator()(const std::unique_ptr<T>& p) const { return std::hash<id_t>()(p->_id); }
    size_t operator()(const std::shared_ptr<T>& p) const { return std::hash<id_t>()(p->_id); }
}; // hasher

struct state;
using stateptr_t = std::shared_ptr<state>; // break curcular dep between regions & states
using states_t   = std::map<id_t, stateptr_t>;
//using states_t   = std::set<ptr_t, hasher<state>>;

// transition: trigger [guard] /effect
struct transition
{
    id_t _id;
    id_t _fromState;
    id_t _toState;
    id_t _event;  // trigger
    id_t _guard;
    id_t _effect;

    indent& trace(indent& id, std::ostream& os) const;
    
    friend std::ostream& operator<<(std::ostream& os, const transition& t);
}; // transition

//using transitions_t = std::set<transition, hasher<transition>>;
using transitions_t = std::map<id_t, transition>;
using graph_t       = std::map<id_t/*fromState*/, transitions_t>; // TODO: use BGL?


/*
 https://www.omg.org/spec/UML/2.5.1/About-UML
 https://sparxsystems.com/resources/tutorials/uml2/state-diagram.html
 TODO
   initial/final states
   onentry/ onexit
   history states
 
*/

struct region
{
    using states_t      = sm::states_t;

    id_t       _id;
    states_t   _substates;

    bool operator==(const region& other) const { return other._id == _id; }

    indent& trace(indent& id, std::ostream& os) const;

    friend std::ostream& operator<<(std::ostream& os, const region& r);
}; // region

using regions_t = std::map<id_t, region>;


struct state
{
    using ptr_t         = sm::stateptr_t;
    using states_t      = sm::states_t;
    using transitions_t = sm::transitions_t;
    using regions_t     = sm::regions_t;
    
    id_t           _id;
    regions_t      _regions;
    transitions_t  _transitions;

    bool operator==(const state& other) const { return other._id == _id; }

    state& add(const state& newState)
    {
        return *this;
    }

    indent& trace(indent& id, std::ostream& os) const;

    friend std::ostream& operator<<(std::ostream& os, const state& s);

}; // state


/*
 * A state machine is a collection of parallel regions (has at least one).
 * A region is a collection of (sub)states with transitions.
 * A state is a collection of regions and has transitions.
 */
struct state_machine
{
    using states_t  = sm::states_t;
    using regions_t = sm::regions_t;
    
    id_t       _id;
    states_t   _substates;
    regions_t  _regions;

    // TODO: do a move one later
    // TODO: add state to last regions
    state& add(const state& newState) 
    {
        assert( ! newState._id.empty());
        auto it = _substates.find(newState._id);
        if (it == _substates.end())
        {
            auto [it, ret] = _substates.emplace(newState._id, std::make_shared<state>());
            *it->second = newState;
        }
        else
        {
            it->second->add(newState);
        }
    }

    indent& trace(indent& id, std::ostream& os) const;

    friend std::ostream& operator<<(std::ostream& os, const state_machine& sm);
}; // state_machine


inline indent& transition::trace(indent& id, std::ostream& os) const
{
    ++id;
    os  << id 
        << _fromState << " --> " << _toState << " " 
        << _event << '[' << _guard << "]/" << _effect
        << " (" << _id << ")\n"
        ;
    --id;
    return id;
}

inline std::ostream& operator<<(std::ostream& os, const transition& t)
{
    indent id("");
    t.trace(id, os);
    return os;
}

inline indent& region::trace(indent& id, std::ostream& os) const
{
    ++id;
    os << id << "-- " << _id << '\n';
    for (const auto& [k, v] : _substates)
    {
        v->trace(id, os);
    }
    --id;
    return id;
}

inline std::ostream& operator<<(std::ostream& os, const region& r)
{
    indent id("");
    r.trace(id, os);
    return os;
}

inline indent& state::trace(indent& id, std::ostream& os) const
{
    ++id;
    os << id << "state " << _id << " s{\n";
    for (const auto& [k, v] : _transitions)
    {
        v.trace(id, os);
    }
    for (const auto& [k, v] : _regions)
    {
        v.trace(id, os);
    }
    os << id << "}s\n";
    --id;
    return id;
}

inline std::ostream& operator<<(std::ostream& os, const state& s)
{
    indent id("");
    s.trace(id, os);
    return os;
}


inline indent& state_machine::trace(indent& id, std::ostream& os) const
{
    ++id;
    os << id << "machine " << _id << " m{\n";
    for (const auto& [k, v] : _substates)
    {
        v->trace(id, os);
    }
    for (const auto& [k, v] : _regions)
    {
        v.trace(id, os);
    }
    os << id << "}m\n";
    --id;
    return id;
}

inline std::ostream& operator<<(std::ostream& os, const state_machine& sm)
{
    indent id("");
    sm.trace(id, os);
    return os;
}

} //namespace upml::sm


#endif //#define INCLUDED_state_machine_hpp_6ab84852_1aea_4eb0_8f3c_fd6054e765ea
