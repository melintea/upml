/*
 *  $Id: $
 *
 *  Copyright 2024 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 *  You need a C++0x compiler.
 *
 */

#include "promela_generator.hpp"

#include <algorithm>
#include <chrono>
#include <map>
#include <set>

namespace upml {

namespace spin {

using id_t    = upml::sm::id_t;
using idx_t   = int;
using map_t   = std::map<upml::sm::id_t, idx_t>;

id_t name(const id_t& prefix, const upml::sm::id_t& evt);
id_t name(upml::sm::id_t& evt);
id_t idx(const upml::sm::id_t& s);

// e.g. "event:xyz" or "event_xyz".
struct scoped_name
{
    // TODO: use string slices
    std::string _type;
    std::string _name;

    static scoped_name create(const std::string& scopedName)
    {
        scoped_name t;

        // assumption: there is only one such
        auto sep(scopedName.find(':')); 
        if (sep == std::string::npos) {
            sep = scopedName.find('_');
        }

        if (sep != std::string::npos) {
            t._type = scopedName.substr(0, sep);
            t._name = scopedName.substr(sep+1);
            return t;
        }

        t._name = scopedName;
        return t;
    } // create

    friend std::ostream& operator<<(std::ostream& os, const scoped_name& sn)
    {
        if (sn._type.empty()) {
            os << sn._name << ' ';
        } else {
            os << idx(name(sn._type, sn._name)) << ' ';
        }
        return os;
    }
};

// TODO: fold these into Visitor?
id_t name(const id_t& prefix, const upml::sm::id_t& evt)
{
    std::string sep = evt.length() && evt[0] != '_' ? "_" : "";
    return prefix 
           + sep 
           + evt;
}

id_t name(upml::sm::id_t& evt)
{
    // assumption: there is only one such
    auto sep(evt.find(':')); 
    if (sep == std::string::npos) {
        sep = evt.find('_');
    }

    if (sep == std::string::npos) {
        return evt;
    } else {
        return name(evt.substr(0, sep), evt.substr(sep+1));
    }
}

map_t names(const id_t& prefix, const upml::sm::names_t& evts)
{
    map_t ret;
    idx_t i(0);
    for (const auto& e : evts) {
        scoped_name te(scoped_name::create(e));
        ret[name(prefix, te._name)] = i++;
    }
    return ret;
}

id_t event(const upml::sm::id_t& evt)
{
    return name("event", evt);
}

map_t events(const upml::sm::names_t& ss)
{
    return names("event", ss);
}

id_t state(const upml::sm::id_t& evt)
{
    return name("state", evt);
}

map_t states(const upml::sm::names_t& ss)
{
    return names("state", ss);
}

id_t region(const upml::sm::id_t& r)
{
    return name("region", r);
}

id_t region(const upml::sm::id_t& r, const upml::sm::id_t& ownerTag)
{
    return region(r) + '_' + ownerTag;
}

map_t regions(const upml::sm::names_t& ss)
{
    return names("region", ss);
}

id_t idx(const upml::sm::id_t& s)
{
    return name("idx", s);
}

class Visitor
{
    upml::sm::state_machine& _sm;
    std::ostream&            _out;
    map_t  _events;
    map_t  _states;
    map_t  _regions;

public: 

    Visitor(upml::sm::state_machine& sm,
            std::ostream&             out);
    Visitor()                          = delete;
    ~Visitor()                         = default;
    Visitor(const Visitor&)            = delete;
    Visitor& operator=(const Visitor&) = delete;
    Visitor(Visitor&&)                 = delete;
    Visitor& operator=(Visitor&&)      = delete;

    const upml::sm::region* monitor_region() const
    {
        const upml::sm::region* pr(_sm.owner_region("StateMachineEventGenerator"));
        return pr;
    }

    void visit() const;
    void visit_region(const upml::sm::region& r, const id_t& ownerTag) const;
    void visit_invariants(const upml::sm::region&  r) const;
    void visit_preconditions(const upml::sm::region&  r) const;
    void visit_postconditions(const upml::sm::region&  r) const;
    void visit_state(const upml::sm::state& s) const;
    void visit_invariants(const upml::sm::state& s) const;
    void visit_preconditions(const upml::sm::state& s) const;
    void visit_postconditions(const upml::sm::state& s) const;
    void visit_exit_activities(const upml::sm::state& s) const;
    void visit_entry_activities(const upml::sm::state& s) const;
    void visit_initial_entry_activities(const upml::sm::state& s) const;
    void visit_timeout(const upml::sm::state& s) const;
    void visit_transitions(const upml::sm::state& s) const;
    void visit_transition(
        const upml::spin::id_t&     idxCrtState,
        const upml::sm::transition& t) const;
    void visit_effect(
        const upml::spin::id_t&     idxCrtState,
        const upml::sm::transition& t) const;
    void visit_guard(
        const upml::spin::id_t&     idxCrtState,
        const upml::sm::transition& t) const;
    void visit_activity(
        const upml::spin::id_t&   idxCrtState,
        const upml::sm::activity& a) const;
}; // Visitor

Visitor::Visitor(upml::sm::state_machine& sm,
                 std::ostream&             out)
    : _sm(sm)
    , _out(out)
{
    _events  = names("", sm.events());

    if (sm._addMonitor) {
        _events.emplace(name("", "StateChange"), _events.size());

        if ( ! monitor_region()) {
            const auto r0 = upml::sm::tag(upml::sm::region::_tag, 0);
            auto [itR, dummyR] = _sm._regions.emplace(r0, upml::sm::region{
                ._id = r0
            });

            const auto s0 = "StateMachineEventGenerator";
            auto [itS, dummyS] = itR->second._substates.emplace(
                s0, 
                std::make_shared<upml::sm::state>(upml::sm::state{
                    ._id = s0
                }));
        }
    }

    _regions = names("", sm.regions(true));
    _states  = names("", sm.states(true));
}

void Visitor::visit_state(const upml::sm::state& s) const
{
    int myIdx(_states.find(s._id)->second);

    for (const auto& [k, r] : s._regions) {
        visit_region(r, s._id);
    }
}

void Visitor::visit_activity(
    const upml::spin::id_t&   idxCrtState,
    const upml::sm::activity& a) const
{
    assert("send" == a._args[upml::sm::activity::_argOrder::aoActivity]);
    const auto toSt(scoped_name::create(a._args[upml::sm::activity::_argOrder::aoState]));
    assert(toSt._type == "state");
    const auto* destReg(_sm.owner_region(toSt._name));
    assert(destReg);
    const auto evt(scoped_name::create(a._args[upml::sm::activity::_argOrder::aoEvent]));
    assert(evt._type == "event");

    _out << " send_event(" << idx(region(destReg->_id))
         << ", " << event(evt._name)
         << ", " << idxCrtState
         << ", " << idx(state(toSt._name))
         << "); \n";
}

void Visitor::visit_guard(
    const upml::spin::id_t&     idxCrtState,
    const upml::sm::transition& t) const
{
    if (t._guard.empty()) {
        return;
    }

    _out << " && ";
    for (const auto& tok: t._guard) {
        const auto ttok(scoped_name::create(tok));
        _out << ttok;
    }
}

void Visitor::visit_effect(
    const upml::spin::id_t&     idxCrtState,
    const upml::sm::transition& t) const
{
    if (t._effect.empty()) {
        return;
    }

    upml::sm::activity a = {
        ._id       = upml::sm::tag(upml::sm::activity::_tag, t._line),
        ._state    = idxCrtState,
        ._activity = t._effect[0],
        ._args      = upml::sm::activity::args(t._effect.begin(), t._effect.end())
    };
    visit_activity( idxCrtState, a);
}

void Visitor::visit_transition(
    const upml::spin::id_t&     idxCrtState,
    const upml::sm::transition& t) const
{
    const auto evt(scoped_name::create(t._event));
    const auto toSt(scoped_name::create(t._toState));

    _out << "    //" << t;
    _out << "    :: (crtState == " << idxCrtState
         << " && evtRecv.evId == " << event(evt._name); 
         visit_guard(idxCrtState, t);
    _out << ") -> newState = " << idx(state(toSt._name)) << "; ";
         visit_effect(idxCrtState, t);
    _out << "\n";
}

void Visitor::visit_transitions(const upml::sm::state& s) const
{
    const int myIdx(_states.find(s._id)->second);
    const auto idxCrtState(idx(state(s._id)));

    _out << " \n    /* state " << idxCrtState << "[*/\n";

    visit_invariants(s);
    visit_preconditions(s);

    if ( ! s._transitions.empty()) {
        _out << "\n    /* transitions " << idxCrtState << "[*/\n"
             << "    if\n";
        for (const auto& [k, t] : s._transitions) {
           visit_transition(idxCrtState, t);
        }
        visit_timeout(s);
        _out << "    :: else \n"
             << "    fi\n"
             << "    /*]transitions " << idxCrtState << "*/\n"
             ;
    }

    visit_postconditions(s);
    visit_invariants(s);

    _out << " \n    /*]state " << idxCrtState << "*/\n";
}

void Visitor::visit_entry_activities(const upml::sm::state& s) const
{
    const int myIdx(_states.find(s._id)->second);
    const auto idxCrtState(idx(state(s._id)));

    if ( ! s._activities.empty()) {
        for (const auto& a : s._activities) {
            if (a._args[upml::sm::activity::_argOrder::aoActivity] == "send") {
                if (a._activity == "entry") {
                    _out << "    //" << a;
                    _out << "    :: (newState == " << idxCrtState << ") -> ";
                    visit_activity(idxCrtState, a);
                }
            }
        }
    }
}

// TODO: use never of a watch process
void Visitor::visit_invariants(const upml::sm::region&  r) const
{
}

// TODO: use never of a watch process
void Visitor::visit_invariants(const upml::sm::state&  s) const
{
    if ( ! s._activities.empty()) {
        for (const auto& a : s._activities) {
            if (a._activity == "invariant") {
                _out << "\n    //" << a;
                _out << "    assert(";
                for (const auto& tok: a._args) {
                    const auto ttok(scoped_name::create(tok));
                    _out << ttok;
                }
                _out << ");\n";
            }
        }
    }
}

void Visitor::visit_preconditions(const upml::sm::region&  r) const
{
}

void Visitor::visit_preconditions(const upml::sm::state&  s) const
{
    if ( ! s._activities.empty()) {
        for (const auto& a : s._activities) {
            if (a._activity == "precondition") {
                _out << "\n    //" << a;
                _out << "    assert(";
                for (const auto& tok: a._args) {
                    const auto ttok(scoped_name::create(tok));
                    _out << ttok;
                }
                _out << ");\n";
            }
        }
    }
}

void Visitor::visit_postconditions(const upml::sm::region&  r) const
{
}

void Visitor::visit_postconditions(const upml::sm::state&  s) const
{
    if ( ! s._activities.empty()) {
        for (const auto& a : s._activities) {
            if (a._activity == "postcondition") {
                _out << "\n    //" << a;
                _out << "    assert(";
                for (const auto& tok: a._args) {
                    const auto ttok(scoped_name::create(tok));
                    _out << ttok;
                }
                _out << ");\n";
            }
        }
    }
}

void Visitor::visit_timeout(const upml::sm::state& s) const
{
}

void Visitor::visit_initial_entry_activities(const upml::sm::state& s) const
{
    const int myIdx(_states.find(s._id)->second);
    const auto idxCrtState(idx(state(s._id)));

    if ( ! s._activities.empty()) {
        for (const auto& a : s._activities) {
            if (a._args[upml::sm::activity::_argOrder::aoActivity] == "send") {
                if (a._activity == "entry") {
                    _out << "\n    //" << a;
                    _out << "    ";
                    visit_activity(idxCrtState, a);
                }
            }
        }
    }
}

void Visitor::visit_exit_activities(const upml::sm::state& s) const
{
    const int myIdx(_states.find(s._id)->second);
    const auto idxCrtState(idx(state(s._id)));

    if ( ! s._activities.empty()) {
        for (const auto& a : s._activities) {
            if (a._args[upml::sm::activity::_argOrder::aoActivity] == "send") {
                if (a._activity == "exit") {
                    _out << "    //" << a;
                    _out << "    :: (crtState == " << idxCrtState << ") -> ";
                    visit_activity(idxCrtState, a);
                }
            }
        }
    }
}

// TODO: states can be goto labels
void Visitor::visit_region(const upml::sm::region& r, const id_t& ownerTag) const
{
    const int myIdx(_regions.find(r._id)->second);
    const id_t rname(name("region", r._id));
    const id_t llabel(name("loop", r._id));
    const id_t elabel(name("end", r._id));

    id_t initialState("idx_unknown"), finalState("idx_unknown");
    for (const auto& [k, s] : r._substates) {
        if (s->_initial) {
            initialState = idx(state(k));
        }
        if (s->_final) {
            finalState = idx(state(k));
        }
    }

    _out << "\n\nproctype " << name("region", r._id) << "() // " << ownerTag
         << "\n{"
         << "\n    local short myIdx = " << idx(region(r._id)) << ";"
         << "\n    local event evtRecv; "
         << "\n    local short initialState = " << initialState << "; "
         << "\n    local short finalState = " << finalState << "; "
         << "\n    local short crtState = initialState; "
         << "\n    local short newState = initialState; "
         << "\n    bool terminate = false; "
         << "\n"
         ;

    for (const auto& [k, s] : r._substates) {
        if (s->_initial) {
            visit_initial_entry_activities(*s);
            break;
        }
    }

    _out << "\n" << llabel << ":";
    if (finalState == "idx_unknown") {
        _out << "\n" << elabel << ":";
    }
    _out << "\n    _channels[myIdx]?evtRecv; "
         << "\n    printf(\"MSC: > %d " << region(r._id) << " event %e in state %d\\n\", myIdx, evtRecv.evId, crtState); "
         << "\n\n"
         ;
    const auto subregions(r.regions(false));
    for (const auto& sr : subregions) {
        _out << "\n    _channels[" << idx(region(sr)) << "]!evtRecv; "
             << "\n    printf(\"MSC: < %d " << region(r._id) << " event %e in state %d\\n\", myIdx, evtRecv.evId, crtState); "
             ;
    }

    visit_invariants(r);
    visit_preconditions(r);

    if ( ! r._substates.empty()) {
        for (const auto& [k, s] : r._substates) {
            visit_transitions(*s);
        }
    }

    visit_postconditions(r);
    visit_invariants(r);
    
    bool exitActivities(false);
    bool entryActivities(false);
    for (const auto& [k, s] : r._substates) {
        for (const auto& a : s->_activities) {
            if (a._activity == "exit") {
                exitActivities = true;
            }
            if (a._activity == "entry") {
                entryActivities = true;
            }
        }
    }
    if (exitActivities) {
        _out << R"--(

    ///* exit activities [
    if
    :: (newState != crtState) -> 
       if
        )--";
        for (const auto& [k, s] : r._substates) {
            visit_exit_activities(*s);
        }
        _out << R"--(
       :: else
       fi
    :: else
    fi
    ///*] exit activities
        )--";
    } // activities
    if (entryActivities) {
        _out << R"--(

    ///* entry activities [
    if
    :: (newState != crtState) -> 
       if
        )--";
        for (const auto& [k, s] : r._substates) {
            visit_entry_activities(*s);
        }
        _out << R"--(
       :: else
       fi
    :: else
    fi
    ///*] entry activities
        )--";
    } // activities

    if (_sm._addMonitor) {
        const auto* monitorReg(monitor_region());
        assert(monitorReg);
        if (finalState != "idx_unknown") {
            _out << "\n    if"
                 << "\n    :: (newState != crtState) -> send_event(" << idx(region(monitorReg->_id)) 
                 << ", " << event("StateChange")
                 << ", newState, idx_unknown); printf(\"MSC: state change: %d -> %d\\n\", crtState, newState); "
                 << "\n    ::else\n    fi";
        }
    }
    _out << "\n\n    crtState = newState; "
         << "\n    terminate = (crtState == finalState) && (finalState != idx_unknown); "
         << "\n    if"
         << "\n    :: (terminate); printf(\"MSC: " << region(r._id) << " terminating\\n\"); "
         << "\n    :: else -> goto " << llabel << ";"
         << "\n    fi"
         << "\n} // " << rname << "\n";

    for (const auto& [k, s] : r._substates) {
        visit_state(*s);
    }
}

void Visitor::visit() const
{
    const auto now(std::chrono::system_clock::now());
    const auto nt(std::chrono::system_clock::to_time_t(now));

    _out << "/*\n   Generated by UPML v" << UPML_VERSION 
         << "\n   " << std::ctime(&nt)
        ;
    _out << "\n\n" << _sm << "\n*/\n\n";

    _out << "\n#define idx_unknown -1\n";
    for (const auto& [k, s] : _states) {
        _out << "\n#define " << idx(state(k)) << " " << s;
    }

    _out << "\n";
    for (const auto& [k, r] : _regions) {
        _out << "\n#define " << idx(region(k)) << " " << r;
    }

    std::set<upml::sm::id_t> evts;
    for (const auto& [k, e] : _events) {
        evts.insert(event(k));
    }
    _out << "\n\nmtype = { ";
    for (const auto& e : evts) {
        _out << e << ", ";
    }
    _out << "}\n";
    _out << "\ntypedef event {mtype evId; short fromState; short toState};";
    _out << "\n\nchan _channels[" << _regions.size() << "] = [1] of {event};";

    _out << R"--(

inline send_event(channel, evt, fs, ts)
{
    local event evtSend;
    evtSend.evId      = evt;
    evtSend.fromState = fs;
    evtSend.toState   = ts;
    _channels[channel]!evtSend;
}
    )--";

    _out << "\n\nnever {"
         << "\n    do"
         << "\n    :: assert( 1 == 1 ); // never clause cannot be empty";
    for (const auto& [k, r] : _sm._regions) {
        visit_invariants(r);
    }
    _out << "\n    od"
         << "\n} // never\n\n";

    for (const auto& [k, r] : _sm._regions) {
        visit_region(r, _sm._id);
    }

    _out << "\ninit {\n"
        << "    atomic {\n";
    for (const auto& [k, r] : _regions) {
        _out << "        run " << region(k) << "(); \n";
    }
    _out << "    }\n}\n\n/*UPML end*/\n\n";
}

} // spin

bool promela_generator(
    std::ostream&            out,
    upml::sm::state_machine& sm)
{
    spin::Visitor psm(sm, out);
    psm.visit();
    return true;
}

} //namespace upml

