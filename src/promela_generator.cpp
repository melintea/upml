/*
 *  $Id: $
 *
 *  Copyright 2024 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 *  You need a C++0x compiler.
 *
 */

#include "iostream.hpp"
#include "promela_generator.hpp"
#include "reserved_words.hpp"

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
//       state:X:var or state:X@label
struct scoped_name
{
    // TODO: use string slices
    std::string _scope;           // state or event
    std::string _name;            // of the _scope
    char        _itemType = ' ';  // @label or :variable in _name
    std::string _item;

    static scoped_name create(const std::string& scopedName)
    {
        scoped_name t;

        // assumption: there is only one or two such
        auto sep1(scopedName.find_first_of(":_")); 
        if (sep1 == std::string::npos) {
            t._name = scopedName;
            return t;
        }

        auto sep2(scopedName.find_first_of(":@", sep1+1)); 
        if (sep2 == std::string::npos) {
            t._scope = scopedName.substr(0, sep1);
            t._name  = scopedName.substr(sep1+1, sep2-sep1-1);
            return t;
        }

        t._scope     = scopedName.substr(0, sep1);
        t._name      = scopedName.substr(sep1+1, sep2-sep1-1);
        t._itemType  = scopedName[sep2];
        t._item      = scopedName.substr(sep2+1);
        return t;
    } // create

    std::string to_string() const
    {
        if (_scope.empty()) {
            return _name + ' ';
        } else if (_item.empty()) {
            return idx(name(_scope, _name)) + ' ';
        } else {
            return idx(name(_scope, _name)) + ' ';
            //return idx(name(_scope, _name)) + _itemType + _item + ' ';
        }
    }

    // state:xxx => idx_state_xxx
    friend std::ostream& operator<<(std::ostream& os, const scoped_name& sn)
    {
        os << sn.to_string();
        return os;
    }
}; // scoped_name

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
    auto sep(evt.find_first_of(":_")); 

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

    struct RegionData
    {
        id_t _id;
        int  _regionIdx{0};
        id_t _initialState;
        id_t _finalState;
    };

public: 

    Visitor(upml::sm::state_machine& sm,
            std::ostream&            out);
    Visitor()                          = delete;
    ~Visitor()                         = default;
    Visitor(const Visitor&)            = delete;
    Visitor& operator=(const Visitor&) = delete;
    Visitor(Visitor&&)                 = delete;
    Visitor& operator=(Visitor&&)      = delete;

    void visit() const;
    void visit_region(const upml::sm::region& r, const id_t& ownerTag) const;
    void visit_invariants(const upml::sm::region&  r) const;
    void visit_preconditions(const upml::sm::region&  r) const;
    void visit_postconditions(const upml::sm::region&  r) const;
    void visit_state(const upml::sm::state& s, const RegionData& rd) const;
    void visit_state_regions(const upml::sm::state& s) const;
    void visit_invariants(const upml::sm::state& s) const;
    void visit_preconditions(const upml::sm::state& s) const;
    void visit_postconditions(const upml::sm::state& s) const;
    void visit_exit_activities(const upml::sm::state& s) const;
    void visit_entry_activities(const upml::sm::state& s) const;
    void visit_initial_entry_activities(const upml::sm::state& s) const;
    void visit_timeout(const upml::sm::state& s) const;
    void visit_transitions(const upml::sm::state& s, const RegionData& rd) const;
    void visit_transition(
        const upml::sm::state&      s,
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
    void visit_send_activity(
        const upml::spin::id_t&   idxCrtState,
        const upml::sm::activity& a) const;
    void visit_trace_activity(
        const upml::spin::id_t&   idxCrtState,
        const upml::sm::activity& a) const;
    void visit_ltl() const;
    void visit_ltl(const upml::sm::state& s) const;
    // Turn a plantuml token in a guard/post/pre/condition/invariant/ltl into valid Promela.
    std::string token(const std::string& tok) const;
}; // Visitor

Visitor::Visitor(upml::sm::state_machine& sm,
                 std::ostream&            out)
    : _sm(sm)
    , _out(out)
{
    _events  = names("", sm.events());

    _regions = names("", sm.regions(true));
    _states  = names("", sm.states(true));
}

void Visitor::visit_state(const upml::sm::state& s, const RegionData& rd) const
{
    const int myIdx(_states.find(s._id)->second);
    const auto idxCrtState(idx(state(s._id)));
    const id_t ilabel(name("entry", s._id));
    const id_t elabel(name("end", s._id));
    const id_t blabel(name("body", s._id));
    const id_t llabel(name("loop", s._id));
    const id_t plabel(name("progress", s._id)); //TODO:non-progress cycles

    _out << "\n\n/* state " << idxCrtState << "[*/\n"
         << '\n' << ilabel << ':';
    {
        lpt::autoindent_guard indent(_out);
    
        _out << "\ncurrentState = newState;";
        if (  s._config.count("noInboundEvents") 
           || s._transitions.empty()
        ) {
            _out << "\nnoChannel = true;";
        }
    
        _out << '\n';

        visit_preconditions(s);
        //visit_initial_entry_activities(s);
        visit_entry_activities(s);
    }

    _out << "\n\n" << blabel << ':';
    if (s._initial || s._final) {
        _out << "\n" << llabel << ':';
    }
    if (s._config.count("progressTag")) {
        _out << "\n" << plabel << ':';
    }
    {
        lpt::autoindent_guard indent(_out);

        _out << "\nif"
             << "\n:: ( noChannel == false ) -> ";
        if (s._final) {
            _out << elabel << ':'; // TODO: skip completely the channel read 
        }
        _out << "\n    myChan?evtRecv; "
             << "\n    printf(\"MSC: > %d " << region(rd._id) << " event %e in state %d\\n\", myIdx, evtRecv.evId, currentState); "
             << "\n:: else"
             << "\n    evtRecv.evId = " << event(upml::word::NullEvent) << ";"
             ;
        _out << "\nfi\n\n";
        
        //if (s._transitions.empty()) {
        //    _out << "\n/* state " << idxCrtState << " has no transitions */\n";
        //    return;
        //}
        visit_transitions(s, rd);
        visit_postconditions(s);
    }

    _out << "\n/*]state " << idxCrtState << "*/\n";
}

void Visitor::visit_state_regions(const upml::sm::state& s) const
{
    for (const auto& [k, r] : s._regions) {
        visit_region(*r, s._id);
    }
}

void Visitor::visit_activity(
    const upml::spin::id_t&   idxCrtState,
    const upml::sm::activity& a) const
{
    if ("send" == a._args[upml::sm::activity::_argOrder::aoActivity]) {
        return visit_send_activity(idxCrtState, a);
    } else if ("trace" == a._args[upml::sm::activity::_argOrder::aoActivity]) {
        return visit_trace_activity(idxCrtState, a);
    } else {
        std::cerr << "Unsuported: " << a << std::endl; 
    }
}

void Visitor::visit_trace_activity(
    const upml::spin::id_t&   idxCrtState,
    const upml::sm::activity& a) const
{
    _out << "printf(\"";
    std::ranges::copy(a._args.begin()+1, 
                      a._args.end(),
                      std::ostream_iterator<upml::sm::activity::args::value_type>(_out, " "));
    _out << "\\n\"); \n";
}

void Visitor::visit_send_activity(
    const upml::spin::id_t&   idxCrtState,
    const upml::sm::activity& a) const
{
    assert("send" == a._args[upml::sm::activity::_argOrder::aoActivity]);
    const auto toSt(scoped_name::create(a._args[upml::sm::activity::_argOrder::aoState]));
    assert(toSt._scope == "state");
    const auto destRegPtr(_sm.owner_region(toSt._name));
    assert(destRegPtr);
    const auto evt(scoped_name::create(a._args[upml::sm::activity::_argOrder::aoEvent]));
    assert(evt._scope == "event");

    const auto& destStatePtr(_sm.state(toSt._name));
    assert(destStatePtr != nullptr); // unless someone made a typo
    for (const auto& [k, destRegPtr] : destStatePtr->_regions) {
        _out << "send_event(" << idx(region(destRegPtr->_id))
            << ", " << event(evt._name)
            << ", " << idxCrtState
            << ", " << idx(state(toSt._name))
            << "); \n";
    }
}

std::string Visitor::token(const std::string& tok) const
{
    const auto ttok(scoped_name::create(tok));
    if ( ! ttok._item.empty() && ttok._scope == "state") {
        const auto& destStatePtr(_sm.state(ttok._name));
        assert(destStatePtr != nullptr);
        assert(destStatePtr->_regions.size() == 1); // TODO: syntax error if multiple regions
        for (const auto& [k, destRegPtr] : destStatePtr->_regions) {
            return region(destRegPtr->_id) + ttok._itemType/*:*/ + ttok._item + ' ';
        }
        assert(false);
    }
    else {
        return ttok.to_string();
    }

    assert(false);
    return tok;
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
        _out << token(tok);
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
        ._args     = upml::sm::activity::args(t._effect.begin(), t._effect.end())
    };
    // TODO: UML transition semanic: 
    // - exit old state
    // - generate effect/execute action associated with transition
    // - enter new state
    // unless new state == old state:
    // - self-transitions (exit & enter again) not supported; implemented as internal
    //_out << "currentState = idx_unknown; "; 
    visit_activity( idxCrtState, a);
}

void Visitor::visit_transition(
    const upml::sm::state&      s,
    const upml::sm::transition& t) const
{
    const auto evt(scoped_name::create(t._event));
    const auto toSt(scoped_name::create(t._toState));
    const auto idxCrtState(idx(state(s._id)));

    lpt::autoindent_guard indent(_out);

    _out << "\n//" << t << '\n';
    _out << ":: (evtRecv.evId == " << event(evt._name); 
         visit_guard(idxCrtState, t);
    _out << ") -> ";
         visit_effect(idxCrtState, t);
    if (idx(state(toSt._name)) == idxCrtState) {
        visit_postconditions(s);
        lpt::autoindent_guard indent(_out);
        _out << "\nnewState = " << idx(state(toSt._name)) << "; ";
        _out << "\ngoto " << name("body", s._id) << ';';
    } else {
        visit_exit_activities(s);
        visit_postconditions(s);
        lpt::autoindent_guard indent(_out);
        _out << "\nnewState = " << idx(state(toSt._name)) << "; ";
        _out << "\ngoto " << name("entry", toSt._name) << ';';
    }
    _out << "\n";
}

void Visitor::visit_transitions(const upml::sm::state& s, const RegionData& rd) const
{
    const int myIdx(_states.find(s._id)->second);
    const auto idxCrtState(idx(state(s._id)));

    if ( ! s._transitions.empty()) {
        _out << "\n/* transitions " << idxCrtState << "[*/"
             << "\nif\n";
        for (const auto& [k, t] : s._transitions) {
           visit_transition(s, t);
        }
        visit_timeout(s);
        //TODO: resend unhandled events to the hierarchical parent state
        _out << "\nfi"
             << "\n/*]transitions " << idxCrtState << "*/\n"
             ;
    }

    visit_postconditions(s);
}

void Visitor::visit_entry_activities(const upml::sm::state& s) const
{
    const int myIdx(_states.find(s._id)->second);
    const auto idxCrtState(idx(state(s._id)));

    if ( ! s._activities.empty()) {
        for (const auto& a : s._activities) {
            if ( ! a._args.size() ) {
                std::cerr << "Warning: activity with no args:\n"<< a << "\n";
                continue;
            }
            if (a._activity == "entry") {
                _out << "\n//" << a << '\n';
                //_out << "    :: (newState == " << idxCrtState << ") -> ";
                visit_activity(idxCrtState, a);
            }
        }
    }
}

void Visitor::visit_invariants(const upml::sm::region&  r) const
{
    for (const auto& [k, s] : r._substates) {
        visit_invariants(*s);
    }
}

void Visitor::visit_invariants(const upml::sm::state&  s) const
{
    if ( ! s._activities.empty()) {
        for (const auto& a : s._activities) {
            if (a._activity == "invariant") {
                _out << "\n//" << a << '\n';
                _out << ":: atomic { !(";
                for (const auto& tok: a._args) {
                    _out << token(tok);
                }
                _out << ") -> assert(";
                for (const auto& tok: a._args) {
                    _out << token(tok);
                }
                _out << ") };\n";
            }
        }
    }

    for (const auto& [k, r] : s._regions) {
        visit_invariants(*r);
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
                _out << "\n//" << a << '\n';
                _out << "assert(";
                for (const auto& tok: a._args) {
                    _out << token(tok);
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
                _out << "\n//" << a << '\n';
                _out << "assert(";
                for (const auto& tok: a._args) {
                    _out << token(tok);
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

    if ( ! s._initial) {
        return;
    }

    if ( ! s._activities.empty()) {
        for (const auto& a : s._activities) {
            if (a._activity == "entry") {
                _out << "\n//" << a << '\n';
                visit_activity(idxCrtState, a);
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
            if ( ! a._args.size() ) {
                std::cerr << "Warning: activity with no args:\n"<< a << "\n";
                continue;
            }
            if (a._activity == "exit") {
                _out << "\n//" << a << '\n';
                _out << ":: (currentState == " << idxCrtState << ") -> ";
                visit_activity(idxCrtState, a);
            }
        }
    }
}

void Visitor::visit_region(const upml::sm::region& r, const id_t& ownerTag) const
{
    RegionData regionData;
    regionData._id        = r._id;
    regionData._regionIdx = _regions.find(r._id)->second; // TODO: this is always 0 - wrong
    const id_t rname(name("region", r._id));

    regionData._initialState = "idx_unknown";
    regionData._finalState   = "idx_unknown";
    for (const auto& [k, s] : r._substates) {
        if (s->_initial) {
            regionData._initialState = idx(state(k));
        }
        if (s->_final) {
            regionData._finalState = idx(state(k));
        }
    }

    _out << "\n\nproctype " << rname << "() // " << ownerTag
         << "\n{"
         << "\n    local short myIdx = " << idx(region(r._id)) << ";"
         << "\n    local chan myChan = _channels[myIdx]; xr myChan; "
         << "\n    local event evtRecv; "
         << "\n    local short initialState = " << regionData._initialState << "; "
         << "\n    local short finalState = " << regionData._finalState << "; "
         << "\n    local short currentState = initialState; "
         << "\n    local short newState = initialState; "
         << "\n    local bool noChannel = false; "
         << "\n"
         ;

    visit_preconditions(r);

    for (const auto& [k, s] : r._substates) {
        if (s->_initial) {
            assert(idx(state(k)) == regionData._initialState);
            visit_state(*s, regionData);
            break;  //only one such (supposedly)
        }
    }

    for (const auto& [k, s] : r._substates) {
        if (s->_initial || s->_final) {
            continue;
        }
        visit_state(*s, regionData);
    }

    for (const auto& [k, s] : r._substates) {
        if (s->_final) {
            assert(idx(state(k)) == regionData._finalState);
            visit_state(*s, regionData);
            break;  //only one such (supposedly)
        }
    }

    visit_postconditions(r);

    _out << "\n} // " << rname << ' ' << ownerTag << "\n";


    for (const auto& [k, s] : r._substates) {
        visit_state_regions(*s);
    }
}

void Visitor::visit_ltl(const upml::sm::state& s) const
{
    if (s._activities.empty()) {
        return;
    }
    for (const auto& a : s._activities) {
        //std::cerr << s._id << "activity: " << a << '\n';
        if ( ! a._args.size() ) {
            continue;
        }
        if (a._activity != "ltl") {
            continue;
        }

        _out << "//" << a << '\n';
        _out << "ltl ";
        for (const auto& tok: a._args) {
            auto item(token(tok));
            _out << item << ' ';
        }
        _out << ";\n ";
    }
}

void Visitor::visit_ltl() const
{
    // LTLs are model-wide but plantuml forces ltl inside a state as an activity.
    // Any state would do but for now assume only the closed environment/top ones have ltl clauses
    _out << "\n// ltl claims: run with spin -ltl xyz or spin -noclaim \n";
    for (const auto& [k, r] : _sm._regions) {
        //std::cerr << r->_id << '\n';
        for (const auto& [k, s] : r->_substates) {
            //std::cerr << s->_id << '\n';
            visit_ltl(*s);
            for (const auto& [k, r2] : s->_regions) {
                //std::cerr << r2->_id << '\n';
                for (const auto& [k, s2] : r2->_substates) {
                    visit_ltl(*s2);
                }
            }
        }
    }
    _out << "\n\n";
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
    _out << "\n\nchan _channels[" << _regions.size() << "] = [" << _regions.size() << "] of {event};";

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

    for (const auto& [k, r] : _sm._regions) {
        visit_region(*r, _sm._id);
    }

    // Reserve the never clause for LTL, non-progress checks and such; use a proctype instead
    // See also: spin -O 
    _out << "\n\nproctype invariants() {"
         << "\nend_invariants:"
         << "\nprogress_invariants:"
         ;
    {
        lpt::autoindent_guard indent(_out);

        _out << "\ndo"
            << "\n:: ! (1 != 2) -> assert(false); // ensure at least one statement\n"
            ;
        // Per the doc, remoterefs proc[0]@label or proc[x]:var are valid 
        // only in a never claim but this is accepted with spin 6.5.2
        for (const auto& [k, r] : _sm._regions) {
            visit_invariants(*r);
        }
    }
    _out << "\nod\n} // invariants\n\n";

    _out << "\ninit {\n"
        << "    atomic {\n";
    for (const auto& [k, r] : _regions) {
        _out << "        run " << region(k) << "(); \n";
    }
    _out <<     "        run invariants(); \n";
    _out <<     "    }\n";
    _out <<     "    //(_nr_pr == 1); \n";

    _out <<     "} // init\n\n";

    visit_ltl();

    _out <<     "/*UPML end*/\n\n";
}

bool generate(
    std::ostream&            out,
    upml::sm::state_machine& sm)
{
    spin::Visitor psm(sm, out);
    psm.visit();
    return true;
}

} // spin

} //namespace upml

