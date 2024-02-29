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
#include <iostream>
#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>

namespace upml::sm {


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
}; // hasher


// transition: trigger [guard] /effect
struct transition
{
    using transitions_t = std::unordered_set<transition, hasher<transition>>;
    using graph_t       = std::unordered_map<id_t/*fromState*/, transitions_t>; // TODO: use BGL?
    
    id_t _id;
    id_t _fromState;
    id_t _toState;
    id_t _trigger;
    id_t _guard;
    id_t _effect;

    indent& trace(indent& id, std::ostream& os) const
    {
        ++id;
        os << id 
           << _fromState << " --> " << _toState << " " 
           << _trigger << '[' << _guard << "]/" << _effect
           << " (" << _id << ")\n"
           ;
	    --id;
        return id;
    }
    
    friend std::ostream& operator<<(std::ostream& os, const transition& t);
}; // transition


inline std::ostream& operator<<(std::ostream& os, const transition& t)
{
    indent id("");
    t.trace(id, os);
    return os;
}

/*
 https://www.omg.org/spec/UML/2.5.1/About-UML
 https://sparxsystems.com/resources/tutorials/uml2/state-diagram.html
 TODO
   initial/final states
   onentry/ onexit
   history states
 
*/
struct state
{
    using ptr_t         = std::unique_ptr<state>;
    using states_t      = std::unordered_set<ptr_t, hasher<state>>;
    using transitions_t = transition::transitions_t;
    
    struct region
    {
        id_t       _id;
        states_t   _substates;

        struct hasher
        {
            size_t operator()(const region& s) const { return std::hash<id_t>()(s._id); }
        }; // hasher

        bool operator==(const region& other) const { return other._id == _id; }

        indent& trace(indent& id, std::ostream& os) const
        {
            ++id;
            os << id << "-- " << _id << '\n';
	        std::for_each(_substates.begin(), _substates.end(), 
                          [&id, &os](const auto& pss){ pss->trace(id, os);});
            --id;
            return id;
        }
        friend std::ostream& operator<<(std::ostream& os, const region& r);
    }; // region
    using regions_t = std::unordered_set<region, hasher<region>>;
    
    id_t           _id;
    regions_t      _regions;
    transitions_t  _transitions;

    bool operator==(const state& other) const { return other._id == _id; }

    indent& trace(indent& id, std::ostream& os) const
    {
        ++id;
        os << id << "state " << _id << " s{\n";
        std::for_each(_transitions.begin(), _transitions.end(), 
                      [&id, &os](const auto& t){ t.trace(id, os);});
        std::for_each(_regions.begin(), _regions.end(), 
                      [&id, &os](const auto& r){ r.trace(id, os);});
        os << id << "}s\n";
        --id;
        return id;
    }
    friend std::ostream& operator<<(std::ostream& os, const state& s);

}; // state


inline std::ostream& operator<<(std::ostream& os, const state::region& r)
{
    indent id("");
    r.trace(id, os);
    return os;
}

inline std::ostream& operator<<(std::ostream& os, const state& s)
{
    indent id("");
    s.trace(id, os);
    return os;
}


/*
 *
 */
struct state_machine
{
    using states_t = state::states_t;
    
    id_t       _id;
    states_t   _substates;

    indent& trace(indent& id, std::ostream& os) const
    {
        ++id;
        os << id << "machine " << _id << " m{\n";
        std::for_each(_substates.begin(), _substates.end(), 
                        [&id, &os](const auto& pss){ pss->trace(id, os);});
        os << id << "}m\n";
        --id;
        return id;
    }
    friend std::ostream& operator<<(std::ostream& os, const state_machine& sm);
}; // state_machine

inline std::ostream& operator<<(std::ostream& os, const state_machine& sm)
{
    indent id("");
    sm.trace(id, os);
    return os;
}



} //namespace upml::sm


#endif //#define INCLUDED_state_machine_hpp_6ab84852_1aea_4eb0_8f3c_fd6054e765ea
