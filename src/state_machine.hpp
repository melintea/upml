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
#include <vector>

namespace upml::sm {

using id_t      = std::string;
using names_t   = std::set<id_t>;


inline id_t tag(char c, int num)
{
    //return std::vformat("{}{}", std::make_format_args(c, num));
    return std::string(1, c) + std::to_string(num);
}

struct location
{
    size_t      _line{0};
    size_t      _col{0};
    std::string _file;

    friend std::ostream& operator<<(std::ostream& os, const location& l);
};

inline std::ostream& operator<<(std::ostream& os, const location& l)
{
    os << "F:'" << l._file << "';L:" << l._line << ";C:" << l._col;
    return os;
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


// helper
template <typename T> struct hasher
{
    size_t operator()(const T& s) const { return std::hash<id_t>()(s._id); }
    size_t operator()(const std::unique_ptr<T>& p) const { return std::hash<id_t>()(p->_id); }
    size_t operator()(const std::shared_ptr<T>& p) const { return std::hash<id_t>()(p->_id); }
}; // hasher

struct state;
using stateptr_t = std::shared_ptr<state>; // break circular dep between regions & states
using states_t   = std::map<id_t, stateptr_t>;
//using states_t   = std::set<ptr_t, hasher<state>>;

struct event 
{
    static constexpr const char _tag = 'e';

    id_t _id;
};

// transition: trigger [guard] /effect
struct transition : public location
{
    static constexpr const char _tag = 't';

    using guard  = std::vector<std::string>;
    using effect = std::vector<std::string>;

    id_t   _id;
    id_t   _fromState;
    id_t   _toState;
    id_t   _event;  // trigger
    guard  _guard;
    effect _effect;

    indent& trace(indent& id, std::ostream& os) const;
    
    friend std::ostream& operator<<(std::ostream& os, const transition& t);
}; // transition

//using transitions_t = std::set<transition, hasher<transition>>;
using transitions_t = std::map<id_t, transition>;
using graph_t       = std::map<id_t/*fromState*/, transitions_t>; // TODO: use BGL?

struct activity : public location
{
    static constexpr const char _tag = 'a';
    enum _argOrder{
        aoActivity = 0,  // send
        aoEvent    = 1,  // ACK
        aoIgnore   = 2,  // to
        aoState    = 3,  // Bob
    };
    using args = std::vector<std::string>;

    id_t _id;
    id_t _state;     // owner
    id_t _activity;  // entry, exit, precondition, postcondition, invariant, timeout
    args _args;      // specific to each type of _activity

    indent& trace(indent& id, std::ostream& os) const;
    
    friend std::ostream& operator<<(std::ostream& os, const activity& t);
}; // activity

using activities_t = std::vector<activity>;


/*
 https://www.omg.org/spec/UML/2.5.1/About-UML
 https://sparxsystems.com/resources/tutorials/uml2/state-diagram.html
 TODO
   initial/final states
   onentry/ onexit
   history states
 
*/

struct region : public location
{
    using states_t      = sm::states_t;

    static constexpr const char _tag = 'r';

    id_t       _id;
    states_t   _substates;

    names_t events() const;
    names_t states(bool recursive)  const;
    names_t regions(bool recursive) const;

    bool operator==(const region& other) const { return other._id == _id; }

    stateptr_t state(const id_t& state) const;
    
    indent& trace(indent& id, std::ostream& os) const;

    friend std::ostream& operator<<(std::ostream& os, const region& r);
}; // region

using regions_t = std::map<id_t, region>;


struct state : public location
{
    using ptr_t         = sm::stateptr_t;
    using states_t      = sm::states_t;
    using transitions_t = sm::transitions_t;
    using regions_t     = sm::regions_t;
    using config_t      = std::set<std::string>;
    
    static constexpr const char _tag = 's';

    id_t           _id;
    regions_t      _regions;
    // transitions are in the default region
    // a simple state should have no explicit regions
    transitions_t  _transitions;
    activities_t   _activities;
    bool           _initial{false};
    bool           _final{false};
    config_t       _config;  // noInboundEvents

    names_t events() const;
    names_t states(bool recursive)  const;
    names_t regions(bool recursive) const;

    //  which region has @param state 
    const region* owner_region(const id_t& state) const;

    bool operator==(const state& other) const { return other._id == _id; }

    indent& trace(indent& id, std::ostream& os) const;

    friend std::ostream& operator<<(std::ostream& os, const state& s);
}; // state


/*
 * A state machine is a collection of parallel regions (has at least one).
 * A region is a collection of (sub)states with transitions.
 * A state is a collection of regions and has transitions.
 */
struct state_machine : public location
{
    using states_t  = sm::states_t;
    using regions_t = sm::regions_t;
    
    static constexpr const char _tag = 'm';

    id_t       _id;
    regions_t  _regions;

    // all events across all regions and states
    names_t events() const;
    names_t states(bool recursive)  const;
    names_t regions(bool recursive) const;

    /// which region contains @param state
    const region* owner_region(const id_t& state) const;

    stateptr_t state(const id_t& state) const;

    indent& trace(indent& id, std::ostream& os) const;

    friend std::ostream& operator<<(std::ostream& os, const state_machine& sm);
}; // state_machine

//-----------------------------------------------------------------------------

inline names_t state::events() const
{
    names_t evts;

    for (const auto& [k, r] : _regions) {
        names_t revts(r.events());
        evts.insert(revts.begin(), revts.end());
    }
    for (const auto& [k, t] : _transitions) {
        evts.insert(t._event);
    }
    for (const auto& a : _activities) {
        if (a._activity == "entry" || a._activity == "exit") {
            //TODO: asert this is a send activity
            evts.insert(a._args[activity::_argOrder::aoEvent]);
        }
    }
    return evts;
}

inline names_t region::events() const
{
    names_t evts;
    for (const auto& [k, s] : _substates) {
        names_t revts(s->events());
        evts.insert(revts.begin(), revts.end());
    }
    return evts;
}

inline names_t state_machine::events() const
{
    names_t evts;
    for (const auto& [k, r] : _regions) {
        names_t revts(r.events());
        evts.insert(revts.begin(), revts.end());
    }
    return evts;
}

inline names_t state::states(bool recursive) const
{
    names_t evts;

    for (const auto& [k, r] : _regions) {
        names_t revts(r.states(recursive));
        evts.insert(revts.begin(), revts.end());
    }
    evts.insert(_id);
    return evts;
}

inline names_t region::states(bool recursive) const
{
    names_t evts;
    for (const auto& [k, s] : _substates) {
        if (recursive) {
            names_t revts(s->states(recursive));
            evts.insert(revts.begin(), revts.end());
        }
        evts.insert(s->_id);
    }
    return evts;
}

inline names_t state_machine::states(bool recursive) const
{
    names_t evts;
    for (const auto& [k, r] : _regions) {
        names_t revts(r.states(recursive));
        evts.insert(revts.begin(), revts.end());
    }
    return evts;
}

inline names_t state::regions(bool recursive) const
{
    names_t evts;
    for (const auto& [k, r] : _regions) {
        names_t revts(r.regions(recursive));
        evts.insert(revts.begin(), revts.end());
        evts.insert(r._id);
    }
    return evts;
}

inline names_t region::regions(bool recursive) const
{
    names_t evts;
    for (const auto& [k, s] : _substates) {
        names_t revts(s->regions(recursive));
        evts.insert(revts.begin(), revts.end());
    }
    return evts;
}

inline names_t state_machine::regions(bool recursive) const
{
    names_t evts;
    for (const auto& [k, r] : _regions) {
        if (recursive) {
            names_t revts(r.regions(recursive));
            evts.insert(revts.begin(), revts.end());
        }
        evts.insert(r._id);
    }
    return evts;
}

inline const region* state::owner_region(const id_t& state) const
{
    for (const auto& [k, r] : _regions) {
        if (r._substates.find(state) != r._substates.end()) {
            return &r;
        }
        for (const auto& [k, s] : r._substates) {
            const region* pr(s->owner_region(state));
            if (pr) {
                return pr;
            }
        }
    }
    return nullptr;
}

inline const region* state_machine::owner_region(const id_t& state) const
{
    for (const auto& [k, r] : _regions) {
        if (r._substates.find(state) != r._substates.end()) {
            return &r;
        }
        for (const auto& [k, s] : r._substates) {
            const region* pr(s->owner_region(state));
            if (pr) {
                return pr;
            }
        }
    }
    return nullptr;
}

inline stateptr_t region::state(const id_t& state) const
{
    for (const auto& [k, s] : _substates) {
        if (k == state) {
            return s;
        }
        for (const auto& [k, r] : s->_regions) {
            stateptr_t pS(r.state(state));
            if (pS) {
                return pS;
            }
        }
    }
    return {};
}

inline stateptr_t state_machine::state(const id_t& state) const
{
    for (const auto& [k, r] : _regions) {
        const auto itS(r._substates.find(state));
        if (itS != r._substates.end()) {
            return itS->second;
        }
        for (const auto& [k, r] : _regions) {
            stateptr_t pS(r.state(state));
            if (pS) {
                return pS;
            }
        }
    }
    return {};
}

//-----------------------------------------------------------------------------
inline std::ostream& operator<<(std::ostream& os, const transition::guard& as)
{
    for (const auto& a : as) {
        os << a << ',';
    }
    return os;
}

inline indent& transition::trace(indent& id, std::ostream& os) const
{
    ++id;
    os  << id 
        << '(' << static_cast<location>(*this) << ") "
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

inline indent& activity::trace(indent& id, std::ostream& os) const
{
    ++id;
    os  << id 
        << '(' << static_cast<location>(*this) << ") "
        << _state << ":" << _activity << ": "
        ;
    std::ranges::copy(_args, std::ostream_iterator<args::value_type>(os, ","));
    os  << " (" << _id << ")\n"
        ;
    --id;
    return id;
}

inline std::ostream& operator<<(std::ostream& os, const activity& a)
{
    indent id("");
    a.trace(id, os);
    return os;
}

inline std::ostream& operator<<(std::ostream& os, const std::pair<std::string, transition>& pt)
{
    os << pt.first << ":" << pt.second;
    return os;
}

inline indent& region::trace(indent& id, std::ostream& os) const
{
    ++id;
    os << id << '(' << static_cast<location>(*this) << ")\n";
    os << id << "-- " << _id << " {\n";
    for (const auto& [k, v] : _substates)
    {
        v->trace(id, os);
    }
    os << id << "}\n";
    --id;
    return id;
}

inline std::ostream& operator<<(std::ostream& os, const region& r)
{
    indent id("");
    r.trace(id, os);
    return os;
}

inline std::ostream& operator<<(std::ostream& os, const std::pair<std::string, region>& pr)
{
    os << pr.first << ":" << pr.second;
    return os;
}


inline indent& state::trace(indent& id, std::ostream& os) const
{
    ++id;
    os << id << '(' << static_cast<location>(*this) << ")\n";
    os << id << "state " << _id 
       << " final:" << _final << ";initial:" << _initial 
       << " {\n";
    for (const auto& [k, v] : _transitions)
    {
        v.trace(id, os);
    }
    for (const auto& v : _activities)
    {
        v.trace(id, os);
    }
    for (const auto& [k, v] : _regions)
    {
        v.trace(id, os);
    }
    if (_config.size())
    {
        ++id;
        os << id;
        for (const auto& cf : _config)
        {
            os << cf << ',';
        }
        os << '\n';
        --id;
    }
    os << id << "}\n";
    --id;
    return id;
}

inline std::ostream& operator<<(std::ostream& os, const state& s)
{
    indent id("");
    s.trace(id, os);
    return os;
}

inline std::ostream& operator<<(std::ostream& os, const stateptr_t& ps)
{
    if (ps) {
        os << *ps;
    } else {
        os << "(NULL)";
    }
    return os;
}

inline std::ostream& operator<<(std::ostream& os, const std::pair<std::string, stateptr_t>& pps)
{
    os << pps.first << ":" << pps.second;
    return os;
}


inline indent& state_machine::trace(indent& id, std::ostream& os) const
{
    ++id;
    os << id << '(' << static_cast<location>(*this) << ")\n";
    os << id << "machine " << _id << " {\n";
    for (const auto& [k, v] : _regions)
    {
        v.trace(id, os);
    }
    os << id << "} " << _id << '\n';
    --id;
    return id;
}

inline std::ostream& operator<<(std::ostream& os, const state_machine& sm)
{
    indent id("");
    sm.trace(id, os);
    return os;
}

inline std::ostream& operator<<(std::ostream& os, const std::pair<std::string, state_machine>& ppsm)
{
    os << ppsm.first << ":" << ppsm.second;
    return os;
}


} //namespace upml::sm


#endif //#define INCLUDED_state_machine_hpp_6ab84852_1aea_4eb0_8f3c_fd6054e765ea
