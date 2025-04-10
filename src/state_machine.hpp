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

#include "iostream.hpp"
#include "keyword.hpp"

#include <algorithm>
#include <cassert>
#include <iostream>
#include <iterator>
#include <memory>
#include <ranges>
#include <span>
#include <string>
#include <map>  // unordered not supported by boost::spirit/phoenix?
#include <set>
#include <utility>
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

// Path from this state (at index zero) up to the root of the state machine.
using statepath_t   = std::vector<stateptr_t>;

struct region;
using regionptr_t = std::shared_ptr<region>; 
using regions_t = std::map<id_t, regionptr_t>;


struct event 
{
    static constexpr const char _tag = 'e';

    id_t _id;
};

// EnterState or ExitState
struct state_change_event
{
    event        _event;
    stateptr_t   _statePtr;
};
using state_to_state_path = std::vector<state_change_event>;

struct state_to_state_transition
{
    state_to_state_path _exitStates;
    state_to_state_path _enterStates;

    friend std::ostream& operator<<(std::ostream& os, const state_to_state_transition& t);
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

    std::ostream& trace(std::ostream& os) const;
    
    friend std::ostream& operator<<(std::ostream& os, const transition& t);
}; // transition

//using transitions_t = std::set<transition, hasher<transition>>;
using transitions_t = std::map<id_t, transition>;
using graph_t       = std::map<id_t/*fromState*/, transitions_t>; // TODO: use BGL?

struct activity : public location
{
    static constexpr const char _tag = 'a';
    enum _argOrder{
        aoActivity = 0,  // send, trace
        aoEvent    = 1,  // ACK (for send)
        aoIgnore   = 2,  // to  (for send)
        aoState    = 3,  // Bob (for send)
    };
    using args = std::vector<std::string>;

    id_t _id;
    id_t _state;     // owner
    id_t _activity;  // entry, exit, precondition, etc
    args _args;      // specific to each type of _activity

    std::ostream& trace(std::ostream& os) const;
    
    friend std::ostream& operator<<(std::ostream& os, const activity& t);
}; // activity

using activities_t = std::vector<activity>;


/*
 https://www.omg.org/spec/UML/2.5.1/About-UML
 https://sparxsystems.com/resources/tutorials/uml2/state-diagram.html
 TODO
   history states
 
*/

struct region : public location
              , public std::enable_shared_from_this<region>
{
    using states_t      = sm::states_t;

    static constexpr const char _tag = 'r';

    id_t       _id;
    stateptr_t _ownedByState;
    states_t   _substates;

    names_t events() const;
    names_t states(bool recursive)  const;
    names_t regions(bool recursive) const;

    bool operator==(const region& other) const { return other._id == _id; }

    stateptr_t state(const id_t& state) const;
    
    std::ostream& trace(std::ostream& os) const;

    friend std::ostream& operator<<(std::ostream& os, const region& r);
    friend std::ostream& operator<<(std::ostream& os, const regionptr_t& r);
}; // region



struct state : public location
             , public std::enable_shared_from_this<state>
{
    using ptr_t         = sm::stateptr_t;
    using states_t      = sm::states_t;
    using transitions_t = sm::transitions_t;
    using regions_t     = sm::regions_t;
    using config_t      = std::set<std::string>;
    
    static constexpr const char _tag = 's';

    id_t           _id;
    ptr_t          _superState;
    regionptr_t    _ownedByRegion;
    regions_t      _regions;
    // transitions are in the default region
    // a simple state should have no explicit regions
    transitions_t  _transitions;
    activities_t   _activities;
    bool           _initial{false};
    bool           _final{false};
    config_t       _config;     // noInboundEvents, progressTag
    statepath_t    _pathToRoot; // excluding this state

    names_t events() const;
    names_t states(bool recursive)  const;
    names_t regions(bool recursive) const;

    // Excludes this state from the path
    const statepath_t& path_to_root();

    //  which region has @param state 
    const regionptr_t owner_region(const id_t& state) const;

    friend bool operator==(const state& left, const state& right);
    friend bool operator==(const stateptr_t& left, const stateptr_t& right);
    friend bool operator==(const state& left, const id_t& right);
    friend bool operator==(const stateptr_t& left, const id_t& right);

    std::ostream& trace(std::ostream& os) const;

    friend std::ostream& operator<<(std::ostream& os, const state& s);
    friend std::ostream& operator<<(std::ostream& os, const stateptr_t& s);
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

    // Configuration options driving code generation for spin & TLA
    struct config
    {
        bool  _allRandom {false};   // Any state can randomly receive any message
    }; //config

    id_t       _id;
    regions_t  _regions;
    config     _config;

    // all events across all regions and states
    names_t events() const;
    names_t states(bool recursive)  const;
    names_t regions(bool recursive) const;

    /// which region contains @param state
    const regionptr_t owner_region(const id_t& state) const;

    stateptr_t state(const id_t& state) const;

    // how many layers under (including!) fromState
    size_t depth(const stateptr_t& fromState = nullptr) const;

    stateptr_t least_common_ancestor(
                    const stateptr_t& fromState, 
                    const stateptr_t& toState, 
                    bool internalTransition = true);
    state_to_state_transition transition(
                    const stateptr_t& fromState, 
                    const stateptr_t& toState,  
                    bool internalTransition = true);

    std::ostream& trace(std::ostream& os) const;

    friend std::ostream& operator<<(std::ostream& os, const state_machine& sm);
}; // state_machine

//-----------------------------------------------------------------------------
inline bool operator==(const state& left, const state& right)
{
    return left._id == right._id;
}

inline bool operator==(const stateptr_t& left, const stateptr_t& right)
{
    return left->_id == right->_id;
}

inline bool operator==(const state& left, const id_t& right)
{
    return left._id == right;
}

inline bool operator==(const stateptr_t& left, const id_t& right)
{
    return left->_id == right;
}

//-----------------------------------------------------------------------------
inline const statepath_t& state::path_to_root() 
{ 
    if (_pathToRoot.empty() && _superState)
    {
        _pathToRoot.push_back(_superState);
        _pathToRoot.insert(_pathToRoot.end(),
                           _superState->path_to_root().begin(), 
                           _superState->path_to_root().end());
    }
    return _pathToRoot; 
}

inline stateptr_t state_machine::least_common_ancestor(
    const stateptr_t& fromState, 
    const stateptr_t& toState,  
    bool internalTransition)
{
    if (fromState == toState) {
        return internalTransition ? fromState : fromState->_superState; 
    }

    const auto& fromStateRootPath(fromState->path_to_root());
    const auto& toStateRootPath(toState->path_to_root());
    for (const auto& fromPtr : fromStateRootPath) {
        for (const auto& toPtr : toStateRootPath) {
            if (fromPtr == toPtr) {
                return fromPtr;
            }
        }
    }
    return {};
}

inline state_to_state_transition state_machine::transition(
    const stateptr_t& fromState, 
    const stateptr_t& toState,  
    bool internalTransition)
{
    state_to_state_transition path;

    if ((fromState == toState) && internalTransition) {
        return {}; 
    }

    const auto& fromStateRootPath(fromState->path_to_root());
    const auto& toStateRootPath(toState->path_to_root() | std::views::reverse);
    const auto& lcaState(least_common_ancestor(fromState, toState, internalTransition));
    assert(lcaState);

    path._exitStates.push_back({keyword::ExitState, fromState});
    for (const auto& exitState : fromStateRootPath) {
        if (exitState == lcaState) {
            break;
        }
        path._exitStates.push_back({keyword::ExitState, exitState});
    }

    size_t nDrop = 1; // for lcaState
    for (const auto& enterState: toStateRootPath) {
        if (enterState == lcaState) {
            break;
        }
        ++nDrop;
    }
    for (const auto& enterState: toStateRootPath | std::views::drop(nDrop)) {
        path._enterStates.push_back({keyword::EnterState, enterState});
    }
    path._enterStates.push_back({keyword::EnterState, toState});

    return path;
}

inline size_t state_machine::depth(const stateptr_t& fromState) const
{
    size_t max = 0;

    if  ( ! fromState) {
        for (const auto& [k, r] : _regions) {
            for (const auto& [k2, s2] : r->_substates) {
                max = 1 + std::max(max, depth(s2));
            }
        }
    } else {
        if (fromState->_regions.empty()) {
            return 1;
        } else {
            for (const auto& [k, r] : fromState->_regions) {
                for (const auto& [k2, s2] : r->_substates) {
                    max = 1 + std::max(max, depth(s2));
                }
            }
        }
    }

    return max;
}

//-----------------------------------------------------------------------------
inline names_t state::events() const
{
    names_t evts;

    for (const auto& [k, r] : _regions) {
        names_t revts(r->events());
        evts.insert(revts.begin(), revts.end());
    }
    for (const auto& [k, t] : _transitions) {
        evts.insert(t._event);
    }
    evts.insert(keyword::NullEvent);
    evts.insert(keyword::EnterState);
    evts.insert(keyword::ExitState);
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
        names_t revts(r->events());
        evts.insert(revts.begin(), revts.end());
    }
    return evts;
}

inline names_t state::states(bool recursive) const
{
    names_t evts;

    for (const auto& [k, r] : _regions) {
        names_t revts(r->states(recursive));
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
        names_t revts(r->states(recursive));
        evts.insert(revts.begin(), revts.end());
    }
    return evts;
}

inline names_t state::regions(bool recursive) const
{
    names_t evts;
    for (const auto& [k, r] : _regions) {
        names_t revts(r->regions(recursive));
        evts.insert(revts.begin(), revts.end());
        evts.insert(r->_id);
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
            names_t revts(r->regions(recursive));
            evts.insert(revts.begin(), revts.end());
        }
        evts.insert(r->_id);
    }
    return evts;
}

inline const regionptr_t state::owner_region(const id_t& state) const
{
    for (const auto& [k, r] : _regions) {
        if (r->_substates.find(state) != r->_substates.end()) {
            return r;
        }
        for (const auto& [k, s] : r->_substates) {
            const regionptr_t pr(s->owner_region(state));
            if (pr) {
                return pr;
            }
        }
    }
    return nullptr;{}
}

inline const regionptr_t state_machine::owner_region(const id_t& state) const
{
    for (const auto& [k, r] : _regions) {
        if (r->_substates.find(state) != r->_substates.end()) {
            return r;
        }
        for (const auto& [k, s] : r->_substates) {
            const regionptr_t pr(s->owner_region(state));
            if (pr) {
                return pr;
            }
        }
    }
    return {};
}

inline stateptr_t region::state(const id_t& state) const
{
    for (const auto& [k, s] : _substates) {
        if (k == state) {
            return s;
        }
        for (const auto& [k, r] : s->_regions) {
            stateptr_t pS(r->state(state));
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
        const auto itS(r->_substates.find(state));
        if (itS != r->_substates.end()) {
            return itS->second;
        }
        for (const auto& [k, r] : _regions) {
            stateptr_t pS(r->state(state));
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

inline std::ostream& transition::trace(std::ostream& os) const
{
    lpt::autoindent_guard indent(os);
    os  << '(' << static_cast<location>(*this) << ") "
        << _fromState << " --> " << _toState << " " 
        << _event << '[' << _guard << "]/" << _effect
        << " (" << _id << ")"
        ;
    return os;
}

inline std::ostream& operator<<(std::ostream& os, const transition& t)
{
    t.trace(os);
    return os;
}

inline std::ostream& operator<<(std::ostream& os, const state_to_state_transition& t)
{
    os << "[*]->";
    std::ranges::for_each(std::as_const(t._exitStates), 
                          [&os](const auto& change) {
                              os << change._event._id << ':' << change._statePtr->_id << "->";
                          });
    os << "[^]->";
    std::ranges::for_each(std::as_const(t._enterStates), 
                          [&os](const auto& change) {
                              os << change._event._id << ':' << change._statePtr->_id << "->";
                          });
    os << "[*]";
    return os;
}

inline std::ostream& activity::trace(std::ostream& os) const
{
    lpt::autoindent_guard indent(os);
    os  << '(' << static_cast<location>(*this) << ") "
        << _state << ":" << _activity << ": "
        ;
    std::ranges::copy(_args, std::ostream_iterator<args::value_type>(os, ","));
    os  << " (" << _id << ")"
        ;
    return os;
}

inline std::ostream& operator<<(std::ostream& os, const activity& a)
{
    a.trace(os);
    return os;
}

inline std::ostream& operator<<(std::ostream& os, const std::pair<std::string, transition>& pt)
{
    os << pt.first << ":" << pt.second;
    return os;
}

inline std::ostream& region::trace(std::ostream& os) const
{
    lpt::autoindent_guard indent(os);
    os << '(' << static_cast<location>(*this) << ")\n";
    os << "-- " << _id << " _ownedByState:" << (_ownedByState ? _ownedByState->_id : "-") << " {\n";
    for (const auto& [k, v] : _substates)
    {
        v->trace(os);
        os << '\n';
    }
    os << "} " <<_id;
    return os;
}

inline std::ostream& operator<<(std::ostream& os, const region& r)
{
    r.trace(os);
    return os;
}

inline std::ostream& operator<<(std::ostream& os, const regionptr_t& rp)
{
    if (rp) {
        os << *rp;
    } else {
        os << "(NULL)";
    }
    return os;
}

inline std::ostream& operator<<(std::ostream& os, const std::pair<std::string, region>& pr)
{
    os << pr.first << ":" << pr.second;
    return os;
}


inline std::ostream& state::trace(std::ostream& os) const
{
    lpt::autoindent_guard indent(os);
    os << '(' << static_cast<location>(*this) << ")\n";
    os << "state " << _id 
       << " final:" << _final << ";initial:" << _initial 
       << ";_superState:" << (_superState ? _superState->_id : "-") 
       << ";_ownedByRegion:" << (_ownedByRegion ? _ownedByRegion->_id : "-") 
       << " {\n";
    for (const auto& [k, v] : _transitions)
    {
        v.trace(os);
        os << '\n';
    }
    for (const auto& v : _activities)
    {
        v.trace(os);
        os << '\n';
    }
    for (const auto& [k, v] : _regions)
    {
        v->trace(os);
        os << '\n';
    }
    if (_config.size())
    {
        {
            lpt::autoindent_guard indent(os);
            for (const auto& cf : _config)
            {
                os << cf << ',';
            }
        }
        os << '\n';
    }
    os << "} " << _id;
    return os;
}

inline std::ostream& operator<<(std::ostream& os, const state& s)
{
    s.trace(os);
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


inline std::ostream& state_machine::trace(std::ostream& os) const
{
    lpt::autoindent_guard indent(os);
    os << '(' << static_cast<location>(*this) << ")\n";
    os << "machine " << _id << " {\n";
    for (const auto& [k, v] : _regions)
    {
        v->trace(os);
        os << '\n';
    }
    os << "} " << _id << '\n';
    return os;
}

inline std::ostream& operator<<(std::ostream& os, const state_machine& sm)
{
    sm.trace(os);
    return os;
}

inline std::ostream& operator<<(std::ostream& os, const std::pair<std::string, state_machine>& ppsm)
{
    os << ppsm.first << ":" << ppsm.second;
    return os;
}


} //namespace upml::sm


#endif //#define INCLUDED_state_machine_hpp_6ab84852_1aea_4eb0_8f3c_fd6054e765ea
