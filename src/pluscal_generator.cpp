/*
 *  $Id: $
 *
 *  Copyright 2024 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 *  You need a C++0x compiler.
 *
 */

#include "pluscal_generator.hpp"

#include <algorithm>
#include <chrono>
#include <map>
#include <numeric>
#include <set>

static std::string indent0 ("\n");
static std::string indent4 ("\n    ");
static std::string indent8 ("\n        ");
static std::string indent12("\n            ");

namespace upml {

namespace tla {

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

    std::string to_string() const
    {
        if (_type.empty()) {
            return _name + ' ';
        } else {
            return idx(name(_type, _name)) + ' ';
        }
    }

    // state:xxx => idx_state_xxx
    friend std::ostream& operator<<(std::ostream& os, const scoped_name& sn)
    {
        os << sn.to_string();
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
    idx_t i(1); // 1-based in TLA
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
        const upml::tla::id_t&      idxCrtState,
        const upml::sm::transition& t) const;
    void visit_guard(
        const upml::tla::id_t&      idxCrtState,
        const upml::sm::transition& t) const;
    void visit_activity(
        const upml::tla::id_t&    idxCrtState,
        const upml::sm::activity& a) const;
    // Turn a plantuml token in a guard/post/pre/condition/invariant into valid PlusCal.
    std::string token(const std::string& tok) const;
}; // Visitor

Visitor::Visitor(upml::sm::state_machine& sm,
                 std::ostream&            out)
    : _sm(sm)
    , _out(out)
{
    _events  = names("", sm.events());
    _events.emplace(name("", "NullEvent"), _events.size());

    _regions = names("", sm.regions(true));
    _states  = names("", sm.states(true));
}

void Visitor::visit_state(const upml::sm::state& s, const RegionData& rd) const
{
    const int myIdx(_states.find(s._id)->second);
    const auto idxCrtState(idx(state(s._id)));
    const id_t ilabel(name("entry", s._id) + ": skip;"); //skip because we cannot have two consecutive labels
    const id_t elabel(name("end", s._id) + ": skip;");
    const id_t blabel(name("body", s._id) + ": skip;");
    const id_t llabel(name("loop", s._id) + ": skip;");
    const id_t plabel(name("progress", s._id) + ": skip;"); //TODO:non-progress cycles

    _out << indent0 << "\n\\* state " << idxCrtState << "[\n";
    _out << indent0 << ilabel 
         << indent4 << "currentState := newState;";
    if (  s._config.count("noInboundEvents") 
       || s._transitions.empty()
    ) {
        _out << indent4 << "noChannel := TRUE;";
    }

    visit_preconditions(s);
    //visit_initial_entry_activities(s);
    visit_entry_activities(s);

    _out << "\n\n" << blabel;
    if (s._initial || s._final) {
        _out << "\n" << llabel;
    }
    if (s._config.count("progressTag")) {
        _out << "\n" << plabel;
    }
    _out << indent4 << "if ( noChannel = TRUE ) {";
    if (s._final) {
        _out << indent0 << elabel; // TODO: skip completely the channel read 
    }
    _out    << indent8 << "recv_event(evtRecv, self); "
            << indent4 << "} else {"
            << indent8 << "evtRecv.evId := " << event("NullEvent") << ";"
            << indent4 << "}"
            << "\n\n"
            ;

    //if (s._transitions.empty()) {
    //    _out << indent0 << "\n/* state " << idxCrtState << " has no transitions */\n";
    //    return;
    //}
    visit_transitions(s, rd);
    visit_postconditions(s);

    _out << indent0 << "\\*]state " << idxCrtState << "\n";
}

void Visitor::visit_state_regions(const upml::sm::state& s) const
{
    for (const auto& [k, r] : s._regions) {
        visit_region(r, s._id);
    }
}

void Visitor::visit_activity(
    const upml::tla::id_t&    idxCrtState,
    const upml::sm::activity& a) const
{
    assert("send" == a._args[upml::sm::activity::_argOrder::aoActivity]);
    const auto toSt(scoped_name::create(a._args[upml::sm::activity::_argOrder::aoState]));
    assert(toSt._type == "state");
    const auto* destReg(_sm.owner_region(toSt._name));
    assert(destReg);
    const auto evt(scoped_name::create(a._args[upml::sm::activity::_argOrder::aoEvent]));
    assert(evt._type == "event");

    const auto& destStatePtr(_sm.state(toSt._name));
    assert(destStatePtr != nullptr); // unless someone made a typo
    for (const auto& [k, destReg] : destStatePtr->_regions) {
        _out << "send_event(" << idx(region(destReg._id))
            << ", " << event(evt._name)
            << ", " << idxCrtState
            << ", " << idx(state(toSt._name))
            << "); \n";
    }
}

std::string Visitor::token(const std::string& tok) const
{
    static const std::map<std::string, std::string> tlaTokens{
        {"&&", "/\\"},
        {"||", "\\/"},
        {"!",  "~"},
        {"==", "="}
    };

    const auto ttok(scoped_name::create(tok));
    if (ttok._type == "currentState") {
        const auto& destStatePtr(_sm.state(ttok._name));
        assert(destStatePtr != nullptr);
        assert(destStatePtr->_regions.size() == 1); // TODO: syntax error if multiple regions
        for (const auto& [k, destReg] : destStatePtr->_regions) {
            return region(destReg._id) + ":" + ttok._type + ' ';
        }
        assert(false);
    }
    else {
        const auto umlTok(ttok.to_string());
        const auto it(tlaTokens.find(umlTok));
        return it != tlaTokens.end() ? it->second : umlTok;
    }

    assert(false);
    return tok;
}

void Visitor::visit_guard(
    const upml::tla::id_t&      idxCrtState,
    const upml::sm::transition& t) const
{
    if (t._guard.empty()) {
        return;
    }

    _out << " /\\ ";
    for (const auto& tok: t._guard) {
        _out << token(tok);
    }
}

void Visitor::visit_effect(
    const upml::tla::id_t&      idxCrtState,
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
    // TODO: UML transition semanic: exit old state, generate effect, enter new state
    // unless new state == old state
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

    _out << indent12 << "\\* " << t;
    _out << indent12 << "await (evtRecv.evId = " << event(evt._name); 
         visit_guard(idxCrtState, t);
    _out << ");" << indent12;
         visit_effect(idxCrtState, t);
    if (idx(state(toSt._name)) == idxCrtState) {
        visit_postconditions(s);
        _out << indent12<< "newState := " << idx(state(toSt._name)) << "; ";
        _out << indent12 << "goto " << name("body", s._id) << ';';
    } else {
        visit_exit_activities(s);
        visit_postconditions(s);
        _out << indent12 << "newState := " << idx(state(toSt._name)) << "; ";
        _out << indent12 << "goto " << name("entry", toSt._name) << ';';
    }
    _out << "\n";
}

void Visitor::visit_transitions(const upml::sm::state& s, const RegionData& rd) const
{
    const int myIdx(_states.find(s._id)->second);
    const auto idxCrtState(idx(state(s._id)));

    if ( ! s._transitions.empty()) {
        _out << indent4 << "\\* transitions " << idxCrtState << "[ "
             << indent4 << "either {";
        auto it = s._transitions.begin();
        do {
           visit_transition(s, it->second);
           ++it;
           if (it != s._transitions.end()) {
               _out << indent4 << "} or {";
           }
        } while (it != s._transitions.end());
        visit_timeout(s);
        _out << indent4 << "}; \\* either"
             << indent4 << "\\*]transitions " << idxCrtState << "\n"
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
            if (a._args[upml::sm::activity::_argOrder::aoActivity] == "send") {
                if (a._activity == "entry") {
                    _out << indent4 << "\\* " << a;
                    _out << indent4;
                    visit_activity(idxCrtState, a);
                }
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
                _out << indent4 << "\\* " << a;
                _out << indent4 << "assert(";
                for (const auto& tok: a._args) {
                    _out << token(tok);
                }
                _out << ");\n";
            }
        }
    }

    for (const auto& [k, r] : s._regions) {
        visit_invariants(r);
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
                _out << indent8 << "\\* " << a;
                _out << "        assert(";
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
                _out << indent8 << "\\* " << a;
                _out << "        assert(";
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
            if (a._args[upml::sm::activity::_argOrder::aoActivity] == "send") {
                if (a._activity == "entry") {
                    _out << indent4 << "\\* " << a;
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
                    _out << indent4 << "\\* " << a;
                    visit_activity(idxCrtState, a);
                }
            }
        }
    }
}

void Visitor::visit_region(const upml::sm::region& r, const id_t& ownerTag) const
{
    RegionData regionData;
    regionData._id        = r._id;
    regionData._regionIdx = _regions.find(r._id)->second; // TODO: this is always 1 - wrong
    const id_t rname(name("region", r._id));

    regionData._initialState = "idx_Unknown";
    regionData._finalState   = "idx_Unknown";
    for (const auto& [k, s] : r._substates) {
        if (s->_initial) {
            regionData._initialState = idx(state(k));
        }
        if (s->_final) {
            regionData._finalState = idx(state(k));
        }
    }

    _out << "\n\nfair+ process (" << rname << " \\in {" << idx(rname) << "}) \\* " << ownerTag
         << "\n    evtRecv = idx_Unknown; "
         << "\n    initialState = " << regionData._initialState << "; "
         << "\n    finalState = " << regionData._finalState << "; "
         << "\n    currentState = initialState; "
         << "\n    newState = initialState; "
         << "\n    noChannel = FALSE; "
         << "\n{"
         << "\nproc_body: skip;" // skip because we cannot have two consecutive labels
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

    _out << "\n} \\* " << rname << ' ' << ownerTag << "\n";


    for (const auto& [k, s] : r._substates) {
        visit_state_regions(*s);
    }
}

void Visitor::visit() const
{
    const auto now(std::chrono::system_clock::now());
    const auto nt(std::chrono::system_clock::to_time_t(now));

    _out << "/*\n   Generated by UPML v" << UPML_VERSION 
         << "\n   " << std::ctime(&nt)
         << "\n\n" << _sm << "\n*/\n"
         << "\n---- MODULE switch ----------------------------------------------------"
         << "\n\nEXTENDS TLC, Integers, Sequences\n"
         ;

    _out << "\nidx_Unknown = -1\n";
    for (const auto& [k, s] : _states) {
        _out << "\n" << idx(state(k)) << " = " << s;
    }

    _out << "\n";
    for (const auto& [k, r] : _regions) {
        _out << "\n" << idx(region(k)) << " = " << r;
    }

    _out << "\n";
    for (const auto& [k, e] : _events) {
        _out << "\n" << idx(event(k)) << " = " << e;
    }

    _out << "\n\n(**********************************************************************"
         << "\n\n--algorithm lamp {\n\nvariables\n"
         ;
    
    std::string chans(std::accumulate(std::next(_regions.begin()), _regions.end(),
                                      std::string("<<>>"),
                                      [](std::string all, const auto& /*reg*/){
                                          return std::move(all + ", <<>>");
                                      }));
    _out << indent4 <<" channels = << " << chans << " >>;\n";

    _out << R"--(

macro send_event(evt, from, to) {
    print <<"P:", from, "o->", evt, " > P:", to>>;
    channels[to] := Append(@, evt);
}
macro recv_event(evt, to) {
    await Len(channels[to]) > 0;
    evt := Head(channels[to]);
    print <<"P:", to, "<-i", evt>>;
    channels[to] := Tail(@);
}

    )--";

    for (const auto& [k, r] : _sm._regions) {
        visit_region(r, _sm._id);
    }

    _out << "\n\n} \\* algorithm lamp"
         << "\n\n**********************************************************************)\n\n"
         ;

} // Visitor::visit

} // tla

bool pluscal_generator(
    std::ostream&            out,
    upml::sm::state_machine& sm)
{
    tla::Visitor psm(sm, out);
    psm.visit();
    return true;
}

} //namespace upml

