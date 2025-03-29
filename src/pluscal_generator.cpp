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
#include "pluscal_generator.hpp"
#include "reserved_words.hpp"

#include <boost/algorithm/string/trim.hpp>

#include <algorithm>
#include <chrono>
#include <map>
#include <numeric>
#include <set>
#include <span>

namespace upml {

namespace tla {

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
    upml::sm::state_machine&  _sm;
    std::ostream&             _out;
    map_t  _events;
    map_t  _states;
    map_t  _regions;
    std::vector<std::string>  _transitionLabels; 
    mutable int               _labelIdx{0}; // Index for send/recv events labels

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
    void visit_invariants(const upml::sm::state& s) const;
    void visit_preconditions(const upml::sm::region&  r) const;
    void visit_postconditions(const upml::sm::region&  r) const;
    void visit_state(const upml::sm::state& s, const RegionData& rd) const;
    void visit_state_regions(const upml::sm::state& s) const;
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
    // collect transition labels into _transitionLabels
    void visit_transition_labels(const upml::sm::region&  r);
    void visit_transition_labels(const upml::sm::state& s);
    void visit_effect(
        const upml::tla::id_t&      idxCrtState,
        const upml::sm::transition& t) const;
    void visit_guard(
        const upml::tla::id_t&      idxCrtState,
        const upml::sm::transition& t) const;
    void visit_activity(
        const upml::tla::id_t&    idxCrtState,
        const upml::sm::activity& a) const;
    void visit_send_activity(
        const upml::tla::id_t&    idxCrtState,
        const upml::sm::activity& a) const;
    void visit_trace_activity(
        const upml::tla::id_t&    idxCrtState,
        const upml::sm::activity& a) const;
    void visit_ltl() const;
    void visit_ltl(const upml::sm::state& s) const;
    // Turn a plantuml token in a guard/post/pre/condition/invariant into valid PlusCal.
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

    for (const auto& [kr, r] : _sm._regions) {
        visit_transition_labels(*r);
    }
}

void Visitor::visit_state(const upml::sm::state& s, const RegionData& rd) const
{
    const int myIdx(_states.find(s._id)->second);
    const auto idxCrtState(idx(state(s._id)));
    const id_t ilabel(name(keyword::entry, s._id) + ": skip;"); //skip because we cannot have two consecutive labels
    const id_t elabel(name("end", s._id) + ": skip;");
    const id_t blabel(name("body", s._id) + ": skip;");
    const id_t llabel(name("loop", s._id) + ": skip;");
    const id_t plabel(name("progress", s._id) + ": skip;"); //TODO:non-progress cycles

    _out << "\n\n\\* state " << idxCrtState << "[\n"
         << '\n' << ilabel; 
    {
        lpt::autoindent_guard indent(_out);

        _out << "\ncurrentState[self] := newState;";
        if (  s._config.count(keyword::noInboundEvents) 
           || s._transitions.empty()
        ) {
            _out << "\nnoChannel := TRUE;";
        }

        _out << '\n';

        visit_preconditions(s);
        //visit_initial_entry_activities(s);
        visit_entry_activities(s);
    }

    _out << "\n\n" << blabel;
    if (s._initial || s._final) {
        _out << "\n" << llabel;
    }
    if (s._config.count(keyword::progressTag)) {
        _out << "\n" << plabel;
    }
    {
        lpt::autoindent_guard indent(_out);

        _out << "\nif ( noChannel = FALSE ) { ";
        if (s._final) {
            _out << elabel; // TODO: skip completely the channel read 
        }
        _out << "\n    " << upml::sm::tag('L', ++_labelIdx) << ":recv_event(evtRecv, self, currentState[self]); "
             << "\n} else {"
             << "\n    " << "evtRecv := " << idx(event(upml::keyword::NullEvent)) << ";"
             << "\n};"
             << "\n\n"
             ;

        //if (s._transitions.empty()) {
        //    _out << "\n/* state " << idxCrtState << " has no transitions */\n";
        //    return;
        //}
        visit_transitions(s, rd);
        visit_postconditions(s);
    }

    _out << "\n\\*]state " << idxCrtState << "\n";
}

void Visitor::visit_state_regions(const upml::sm::state& s) const
{
    for (const auto& [k, r] : s._regions) {
        visit_region(*r, s._id);
    }
}

void Visitor::visit_activity(
    const upml::tla::id_t&    idxCrtState,
    const upml::sm::activity& a) const
{
    if (keyword::send == a._args[upml::sm::activity::_argOrder::aoActivity]) {
        return visit_send_activity(idxCrtState, a);
    } else if (keyword::trace == a._args[upml::sm::activity::_argOrder::aoActivity]) {
        return visit_trace_activity(idxCrtState, a);
    } else {
        std::cerr << "Unsuported: " << a << std::endl; 
    }
}

void Visitor::visit_trace_activity(
    const upml::tla::id_t&    idxCrtState,
    const upml::sm::activity& a) const
{
    _out << "print <<\"";
    std::ranges::copy(a._args.begin()+1, 
                      a._args.end(),
                      std::ostream_iterator<upml::sm::activity::args::value_type>(_out, " "));
    _out << "\", \"\\n\">>; \n";
}

void Visitor::visit_send_activity(
    const upml::tla::id_t&    idxCrtState,
    const upml::sm::activity& a) const
{
    assert(keyword::send == a._args[upml::sm::activity::_argOrder::aoActivity]);
    const auto toSt(scoped_name::create(a._args[upml::sm::activity::_argOrder::aoState]));
    assert(toSt._scope == keyword::state);
    const auto destRegPtr(_sm.owner_region(toSt._name));
    assert(destRegPtr);
    const auto evt(scoped_name::create(a._args[upml::sm::activity::_argOrder::aoEvent]));
    assert(evt._scope == keyword::event);

    const auto& destStatePtr(_sm.state(toSt._name));
    assert(destStatePtr != nullptr); // unless someone made a typo
    for (const auto& [k, destRegPtr] : destStatePtr->_regions) {
        _out << upml::sm::tag('L', ++_labelIdx)
             << ":send_event(" << idx(region(destRegPtr->_id))
             << ", " << idx(event(evt._name))
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
        {"==", "="},
        {"!=", "/="}
    };

    const auto ttok(scoped_name::create(tok));
    if ( ! ttok._item.empty() && ttok._scope == keyword::state) {
        const auto& destStatePtr(_sm.state(ttok._name));
        assert(destStatePtr != nullptr);
        assert(destStatePtr->_regions.size() == 1); // TODO: syntax error if multiple regions
        assert(ttok._itemType == ':'); // TODO: labels
        for (const auto& [k, destRegPtr] : destStatePtr->_regions) {
            return ttok._item + "[" + idx(region(destRegPtr->_id)) + "] ";
        }
        assert(false);
    }
    else {
        auto umlTok(ttok.to_string());
        boost::algorithm::trim(umlTok);
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

    // TODO: loop over individual statements
    std::span stmt(t._effect.begin(), t._effect.end());
    upml::sm::activity a = {
        ._id       = upml::sm::tag(upml::sm::activity::_tag, t._line),
        ._state    = idxCrtState,
        ._activity = stmt[0],
        ._args     = upml::sm::activity::args(stmt.begin(), stmt.end())
    };
    // TODO: UML transition semanic: exit old state, generate effect, enter new state
    // unless new state == old state
    //_out << "currentState[self] = idx_unknown; "; 
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

    _out << "\n\n\\* " << t << '\n';
    _out << "await (evtRecv = " << idx(event(evt._name)); 
         visit_guard(idxCrtState, t);
    _out << ");" ;
         visit_effect(idxCrtState, t);
    _out << "\nvisitedTransitions[\"" << t._id << "\"] := TRUE;\n";

    if (idx(state(toSt._name)) == idxCrtState) {
        visit_postconditions(s);
        _out << "\nnewState := " << idx(state(toSt._name)) << "; ";
        _out << "\ngoto " << name("body", s._id) << ';';
    } else {
        visit_exit_activities(s);
        visit_postconditions(s);
        _out << "\nnewState := " << idx(state(toSt._name)) << "; ";
        _out << "\ngoto " << name(keyword::entry, toSt._name) << ';';
    }
    _out << "\n";
}

void Visitor::visit_transitions(const upml::sm::state& s, const RegionData& rd) const
{
    const int myIdx(_states.find(s._id)->second);
    const auto idxCrtState(idx(state(s._id)));

    if ( ! s._transitions.empty()) {
        _out << "\n\\* transitions " << idxCrtState << "[ "
             << '\n' << upml::sm::tag('L', ++_labelIdx) << ':'
             << '\n' << (s._transitions.size() > 1 ? "" : "\\* ") << "either {";
        auto it = s._transitions.begin();
        do {
           visit_transition(s, it->second);
           ++it;
           if (it != s._transitions.end()) {
               _out <<  "\n} or {";
           }
        } while (it != s._transitions.end());
        visit_timeout(s);
        //TODO: resend unhandled events to the hierarchical parent state
        _out << '\n' << (s._transitions.size() > 1 ? "" : "\\* ") << "}; \\* either"
             << "\n\\*]transitions " << idxCrtState << "\n"
             ;
    }

    visit_postconditions(s);
}


void Visitor::visit_transition_labels(const upml::sm::region&  r) 
{
    for (const auto& [ks, s] : r._substates) {
        visit_transition_labels(*s);
        for (const auto& [kr2, r2] : s->_regions) {
            visit_transition_labels(*r2);
        }
    }
}

void Visitor::visit_transition_labels(const upml::sm::state& s) 
{
    for (const auto& [kt, s] : s._transitions) {
        _transitionLabels.push_back(kt);
    }
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
            if (a._activity == keyword::entry) {
                _out << "\n\\* " << a << '\n';
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
            if (a._activity == keyword::invariant) {
                    lpt::autoindent_guard indent(_out);
                _out << "\n\\* " << a << '\n';
                _out << "/\\ [](";
                for (const auto& tok: a._args) {
                    _out << token(tok);
                }
                _out << ")\n";
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
            if (a._activity == keyword::precondition) {
                _out << "\n\\* " << a << '\n';
                _out << upml::sm::tag('L', ++_labelIdx) << ": assert(";
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
            if (a._activity == keyword::postcondition) {
                _out << "\n\\* " << a << '\n';
                _out << upml::sm::tag('L', ++_labelIdx) << ": assert(";
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
            if (a._activity == keyword::entry) {
                _out << "\n\\* " << a << '\n';
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
            if (a._activity == keyword::exit) {
                _out << "\n\\* " << a << '\n';
                visit_activity(idxCrtState, a);
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
         << "\nvariables"
         << "\n    evtRecv = idx_Unknown; "
         << "\n    initialState = " << regionData._initialState << "; "
         << "\n    finalState = " << regionData._finalState << "; "
         << "\n    newState = initialState; "
         << "\n    noChannel = FALSE; "
         << "\n{"
         << "\nproc_body_" << idx(rname) << ": currentState[self] := initialState;" 
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

void Visitor::visit_ltl(const upml::sm::state& s) const
{
    if (s._activities.empty()) {
        return;
    }
    for (const auto& a : s._activities) {
        if ( ! a._args.size() ) {
            continue;
        }
        if (a._activity != keyword::ltl) {
            continue;
        }

        _out << "\\* " << a << '\n';
        if (a._args.size() < 3) {
            _out << "\\* not enough arguments \n";
            continue;
        }

        _out << *a._args.begin() << " == ";
        for (auto itTok = ++a._args.begin(); 
             itTok != a._args.end();
             ++itTok) {
            auto item(token(*itTok));
            if (item == "{" || item == "}") {
                continue;
            }
            _out << item << ' ';
        }
        _out << "\n ";
    }
}

void Visitor::visit_ltl() const
{
    // LTLs are model-wide but plantuml forces ltl inside a state as an activity.
    // Any state would do but for now assume only the closed environment/top ones have ltl clauses
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
         << "\n\n" << _sm << "\n*/\n"
         << "\n---- MODULE " << _sm._id << " ----------------------------------------------------"
         << "\n\nEXTENDS TLC, Integers, Sequences\n"
         ;

    _out << "\nidx_Unknown == -1\n";
    for (const auto& [k, s] : _states) {
        _out << "\n" << idx(state(k)) << " == " << s;
    }

    _out << "\n";
    for (const auto& [k, r] : _regions) {
        _out << "\n" << idx(region(k)) << " == " << r;
    }

    _out << "\n";
    for (const auto& [k, e] : _events) {
        _out << "\n" << idx(event(k)) << " == " << e;
    }

    _out << "\n\n(**********************************************************************"
         << "\n\n--algorithm " << _sm._id << " {\n\nvariables\n"
         ;
    
    std::string procs(std::accumulate(std::next(_regions.begin()), _regions.end(),
                                      idx(region(_regions.begin()->first)),
                                      [](std::string all, const auto& r){
                                          return std::move(all + ", " + idx(region(r.first)));
                                      }));

    {
        lpt::autoindent_guard indent(_out);

        _out << "\nprocs = { " << procs << " };";
        _out << "\nchannels = [p \\in procs |-> <<>>];";
        _out << "\ncurrentState = [p \\in procs |-> idx_Unknown];";

        std::string tls;
        if (_transitionLabels.empty()) {
            std::cerr << "Warning: no transitions\n";
        } else {
            tls = std::move(std::accumulate(std::next(_transitionLabels.begin()), _transitionLabels.end(),
                                            std::string('"' + *_transitionLabels.begin() + '"'),
                                            [](std::string all, const auto& l){
                                                return std::move(all + ", \"" + l + '"');
                                            }));
        }
        _out << "\nstateTransitions = { " << tls << " };";
        _out << "\nvisitedTransitions = [t \\in stateTransitions |-> FALSE];";

        _out << "\nmaxUmlEvents = -20;  \\* limit the number of UML events in the run";
    }

    _out << R"--(

\* Add to the Properties box of the model
define {
    \* Limit the number of UML events to maxUmlEvents; if reached this will show as a model run error
    MaxEventsReached == 
        /\ [](maxUmlEvents < 0)
    \* Flag dead transitions as errors
    AllTransitionsVisited == 
        /\ <>(\A t \in DOMAIN visitedTransitions : visitedTransitions[t] = TRUE)
    \* As extracted from the plantuml spec:
    UmlInvariants == 
        /\ [](TRUE) \* ensure not empty
    )--";
    for (const auto& [k, r] : _sm._regions) {
        lpt::autoindent_guard indent(_out);
        visit_invariants(*r);
    }
    _out << "\n}; \\* define \n";


    _out << R"--(

macro send_event(channel, evtId, fromState, toState) {
    print <<"P:", fromState, "o->", evtId, channel, " > P:", toState>>;
    channels[channel] := Append(@, evtId);
    maxUmlEvents := maxUmlEvents + 1;
}
macro recv_event(evtId, channel, inState) {
    await Len(channels[channel]) > 0;
    evtId := Head(channels[channel]);
    print <<"P:", channel, inState, "<-i", evtId>>;
    channels[channel] := Tail(@);
}

    )--";

    for (const auto& [k, r] : _sm._regions) {
        visit_region(*r, _sm._id);
    }

    _out << "\n\n} \\* algorithm " << _sm._id
         << "\n\n**********************************************************************)\n\n";
    
    visit_ltl(); //TODO

    _out << "\\* Weakly fair scheduling \n"
            "(* PlusCal options (wf) *) \n"
            "\n\n=======================================================================\n"
         ;

} // Visitor::visit


bool generate(
    std::ostream&            out,
    upml::sm::state_machine& sm)
{
    tla::Visitor psm(sm, out);
    psm.visit();
    return true;
}

} // tla

} //namespace upml

