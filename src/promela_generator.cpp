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

// e.g. "event:xyz" or "event_xyz".
struct typed_name
{
    // TODO: use string slices
    std::string _type;
    std::string _name;

    static typed_name create(const std::string& scopedName)
    {
        typed_name t;

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
    }

};

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
        typed_name te(typed_name::create(e));
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

id_t region(const upml::sm::id_t& evt)
{
    return name("region", evt);
}

map_t regions(const upml::sm::names_t& ss)
{
    return names("region", ss);
}

id_t idx(const upml::sm::id_t& s)
{
    return name("idx", s);
}

struct state_machine
{
    const upml::sm::state_machine& _sm;
    map_t  _events;
    map_t  _states;
    map_t  _regions;

    state_machine(const upml::sm::state_machine& sm)
        : _sm(sm)
        , _events(names("", sm.events()))
        , _states(names("", sm.states(true)))
        , _regions(names("", sm.regions(true)))
    {}
}; // state_machine

void visit(
    std::ostream&            out,
    const upml::sm::region&  r,
    const state_machine&     psm);

void visit(
    std::ostream&            out,
    const upml::sm::state&   s,
    const state_machine&     psm)
{
    int myIdx(psm._states.find(s._id)->second);

    for (const auto& [k, r] : s._regions) {
        spin::visit(out, r, psm);
    }
}

void visit_activity(
    std::ostream&             out,
    const upml::spin::id_t&   idxCrtState,
    const upml::sm::activity& a,
    const state_machine&      psm)
{
    assert("send" == a._args[upml::sm::activity::_argOrder::aoActivity]);
    const auto toSt(typed_name::create(a._args[upml::sm::activity::_argOrder::aoState]));
    assert(toSt._type == "state");
    const auto* destReg(psm._sm.owner_region(toSt._name));
    assert(destReg);
    const auto evt(typed_name::create(a._args[upml::sm::activity::_argOrder::aoEvent]));
    assert(evt._type == "event");

    out << " send_event(" << idx(region(destReg->_id))
        << ", " << event(evt._name)
        << ", " << idxCrtState
        << ", " << idx(state(toSt._name))
        << "); \n";
}

void visit_guard(
    std::ostream&               out,
    const upml::spin::id_t&     idxCrtState,
    const upml::sm::transition& t,
    const state_machine&        psm)
{
    if (t._guard.empty()) {
        return;
    }

    out << " && ";
    for (const auto& tok: t._guard) {
        const auto ttok(typed_name::create(tok));
        if (ttok._type.empty()) {
            out << tok << ' ';
        } else {
            out << idx(name(ttok._type, ttok._name)) << ' ';
        }
    }
}

void visit_effect(
    std::ostream&               out,
    const upml::spin::id_t&     idxCrtState,
    const upml::sm::transition& t,
    const state_machine&        psm)
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
    visit_activity(out, idxCrtState, a, psm);
}

void visit_transition(
    std::ostream&               out,
    const upml::spin::id_t&     idxCrtState,
    const upml::sm::transition& t,
    const state_machine&        psm)
{
    const auto evt(typed_name::create(t._event));
    const auto toSt(typed_name::create(t._toState));

    out << "    //" << t;
    out << "    :: (crtState == " << idxCrtState
        << " && evtRecv.evId == " << event(evt._name); 
        visit_guard(out, idxCrtState, t, psm);
    out << ") -> newState = " << idx(state(toSt._name)) << "; ";
        visit_effect(out, idxCrtState, t, psm);
    out << "\n";
}

void visit_transitions(
    std::ostream&            out,
    const upml::sm::state&   s,
    const state_machine&     psm)
{
    const int myIdx(psm._states.find(s._id)->second);
    const auto idxCrtState(idx(state(s._id)));

    out << " \n    /* state " << idxCrtState << "[*/\n";

    if ( ! s._transitions.empty()) {
        out << "\n    /* transitions " << idxCrtState << "[*/\n"
            << "    if\n";
        for (const auto& [k, t] : s._transitions) {
           visit_transition(out, idxCrtState, t, psm);
        }
        out << "    :: else \n"
            << "    fi\n"
            << "    /*]transitions " << idxCrtState << "*/\n"
            ;
    }

    out << " \n    /*]state " << idxCrtState << "*/\n";
}

// TODO: a real visitor impl
void visit_entry_activities(
    std::ostream&            out,
    const upml::sm::state&   s,
    const state_machine&     psm)
{
    const int myIdx(psm._states.find(s._id)->second);
    const auto idxCrtState(idx(state(s._id)));

    if ( ! s._activities.empty()) {
        for (const auto& a : s._activities) {
            out << "    //" << a;
            if (a._args[upml::sm::activity::_argOrder::aoActivity] == "send") {
                if (a._activity == "entry") {
                    out << "    :: (newState == " << idxCrtState << ") -> ";
                    visit_activity(out, idxCrtState, a, psm);
                }
            }
        }
    }
}

void visit_initial_entry_activities(
    std::ostream&            out,
    const upml::sm::state&   s,
    const state_machine&     psm)
{
    const int myIdx(psm._states.find(s._id)->second);
    const auto idxCrtState(idx(state(s._id)));

    if ( ! s._activities.empty()) {
        for (const auto& a : s._activities) {
            out << "\n    //" << a;
            if (a._args[upml::sm::activity::_argOrder::aoActivity] == "send") {
                if (a._activity == "entry") {
                    out << "    ";
                    visit_activity(out, idxCrtState, a, psm);
                }
            }
        }
    }
}

void visit_exit_activities(
    std::ostream&            out,
    const upml::sm::state&   s,
    const state_machine&     psm)
{
    const int myIdx(psm._states.find(s._id)->second);
    const auto idxCrtState(idx(state(s._id)));

    if ( ! s._activities.empty()) {
        for (const auto& a : s._activities) {
            out << "    //" << a;
            if (a._args[upml::sm::activity::_argOrder::aoActivity] == "send") {
                if (a._activity == "exit") {
                    out << "    :: (crtState == " << idxCrtState << ") -> ";
                    visit_activity(out, idxCrtState, a, psm);
                }
            }
        }
    }
}

void visit(
    std::ostream&            out,
    const upml::sm::region&  r,
    const state_machine&     psm)
{
    const int myIdx(psm._regions.find(r._id)->second);
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

    out << "\n\nproctype " << name("region", r._id) << "()"
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
            visit_initial_entry_activities(out, *s, psm);
            break;
        }
    }

    out << "\n" << llabel << ":";
    if (finalState == "idx_unknown") {
        out << "\n" << elabel << ":";
    }
    out << "\n    _channels[myIdx]?evtRecv; "
        << "\n    printf(\"> %d " << region(r._id) << " event %e in state %d\\n\", myIdx, evtRecv.evId, crtState); "
        << "\n\n"
        ;
    const auto subregions(r.regions(false));
    for (const auto& sr : subregions) {
        out << "\n    _channels[" << idx(region(sr)) << "]!evtRecv; "
            << "\n    printf(\"< %d " << region(r._id) << " event %e in state %d\\n\", myIdx, evtRecv.evId, crtState); "
            ;
    }

    if ( ! r._substates.empty()) {
        for (const auto& [k, s] : r._substates) {
            visit_transitions(out, *s, psm);
        }
    }

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
        out << R"--(

    ///* exit activities [
    if
    :: (newState != crtState) -> 
       if
        )--";
        for (const auto& [k, s] : r._substates) {
            visit_exit_activities(out, *s, psm);
        }
        out << R"--(
       :: else
       fi
    :: else
    fi
    ///*] exit activities
        )--";
    } // activities
    if (entryActivities) {
        out << R"--(

    ///* entry activities [
    if
    :: (newState != crtState) -> 
       if
        )--";
        for (const auto& [k, s] : r._substates) {
            visit_entry_activities(out, *s, psm);
        }
        out << R"--(
       :: else
       fi
    :: else
    fi
    ///*] entry activities
        )--";
    } // activities

    const auto* monitorReg(psm._sm.owner_region("StateMachineEventGenerator"));
    assert(monitorReg);
    if (finalState != "idx_unknown") {
        out << "\n    if"
            << "\n    :: (newState != crtState) -> send_event(" << idx(region(monitorReg->_id)) 
              << ", " << event("StateChange")
              << ", newState, idx_unknown); printf(\"state change: %d -> %d\\n\", crtState, newState); "
            << "\n    ::else\n    fi";
    }
    out << "\n\n    crtState = newState; "
        << "\n    terminate = (crtState == finalState) && (finalState != idx_unknown); "
        << "\n    if"
        << "\n    :: (terminate); printf(\"" << region(r._id) << " terminating\\n\"); "
        << "\n    :: else -> goto " << llabel << ";"
        << "\n    fi"
        << "\n} // " << rname << "\n";

    for (const auto& [k, s] : r._substates) {
        spin::visit(out, *s, psm);
    }
}

void visit(
    std::ostream&                  out,
    const upml::sm::state_machine& sm)
{
    const auto now(std::chrono::system_clock::now());
    const auto nt(std::chrono::system_clock::to_time_t(now));

    out << "/*\n   Generated by UPML v" << UPML_VERSION 
        << "\n   " << std::ctime(&nt)
        ;
    out << "\n\n" << sm << "\n*/\n\n";

    spin::state_machine psm(sm);

    out << "\n#define idx_unknown -1\n";
    for (const auto& [k, s] : psm._states) {
        out << "\n#define " << idx(state(k)) << " " << s;
    }

    out << "\n";
    for (const auto& [k, r] : psm._regions) {
        out << "\n#define " << idx(region(k)) << " " << r;
    }

    std::set<upml::sm::id_t> evts;
    evts.insert(event("StateChange")); // event_StateChange
    for (const auto& [k, e] : psm._events) {
        evts.insert(event(k));
    }
    out << "\n\nmtype = { ";
    for (const auto& e : evts) {
        out << e << ", ";
    }
    out << "}\n";
    out << "\ntypedef event {mtype evId; short fromState; short toState};";
    out << "\n\nchan _channels[" << psm._regions.size() << "] = [1] of {event};";

    out << R"--(


inline send_event(channel, evt, fs, ts)
{
    local event evtSend;
    evtSend.evId      = evt;
    evtSend.fromState = fs;
    evtSend.toState   = ts;
    _channels[channel]!evtSend;
}
    )--";

    for (const auto& [k, r] : psm._sm._regions) {
        spin::visit(out, r, psm);
    }

    out << "\ninit {\n"
        << "    atomic {\n";
    for (const auto& [k, r] : psm._regions) {
        out << "        run " << region(k) << "(); \n";
    }
    out << "    }\n}\n\n/*UPML end*/\n\n";
}

} // spin

bool promela_generator(
    std::ostream&                  out,
    const upml::sm::state_machine& sm)
{
    spin::visit(out, sm);
    return true;
}

} //namespace upml

