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
#include "keyword.hpp"

#include <boost/algorithm/string/trim.hpp>

#include <algorithm>
#include <chrono>
#include <map>
#include <set>
#include <span>

namespace upml {

namespace spin::fsm {

/*
 *  FSM/flat model.
 */ 

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
        if (  sep1 == std::string::npos
           || sep1 == 0 // start with
           ) {
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

// TODO: fold these into PseudoVisitor?
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

class PseudoVisitor
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

    using ActivityProcessor_t = std::function<void(const upml::sm::activity&)>;

public: 

    PseudoVisitor(upml::sm::state_machine& sm,
                  std::ostream&            out);
    PseudoVisitor()                          = delete;
    ~PseudoVisitor()                         = default;
    PseudoVisitor(const PseudoVisitor&)            = delete;
    PseudoVisitor& operator=(const PseudoVisitor&) = delete;
    PseudoVisitor(PseudoVisitor&&)                 = delete;
    PseudoVisitor& operator=(PseudoVisitor&&)      = delete;

    void visit() const;
    void visit_region(const upml::sm::region& r, const id_t& ownerTag) const;
    void visit_state(const upml::sm::state& s, const RegionData& rd) const;
    void visit_state_regions(const upml::sm::state& s) const;
    void visit_transitions(const upml::sm::state& s, const RegionData& rd) const;
    void visit_transition(
        const upml::sm::state&      s,
        const upml::sm::transition& t) const;
    void visit_effect(
        const upml::sm::state&      s,
        const upml::sm::transition& t) const;
    void visit_guard(
        const upml::sm::state&      s,
        const upml::sm::transition& t) const;
    void visit_activity(
        const upml::sm::state&    s,
        const upml::sm::activity& a) const;
    void visit_activity(
        const std::string&         activityType,
        const upml::sm::state&     s) const;
    void visit_activity(
        const std::string&         activityType,
        const ActivityProcessor_t& processor) const;
    void visit_activity(
        const std::string&         activityType,
        const upml::sm::state&     s,
        const ActivityProcessor_t& processor) const;
    // Turn a plantuml token in a guard/post/pre/condition/invariant into valid PlusCal.
    std::string token(const std::string& tok) const;
}; // PseudoVisitor

PseudoVisitor::PseudoVisitor(upml::sm::state_machine& sm,
                 std::ostream&            out)
    : _sm(sm)
    , _out(out)
{
    _events  = names("", sm.events());

    _regions = names("", sm.regions(true));
    _states  = names("", sm.states(true));
}

void PseudoVisitor::visit_state(const upml::sm::state& s, const RegionData& rd) const
{
    const int myIdx(_states.find(s._id)->second);
    const auto idxCrtState(idx(state(s._id)));
    const id_t ilabel(name(keyword::entry, s._id));
    const id_t elabel(name("end", s._id));
    const id_t blabel(name("body", s._id));
    const id_t llabel(name("loop", s._id));
    const id_t plabel(name("progress", s._id)); //TODO:non-progress cycles

    _out << "\n\n/* state " << idxCrtState << "[*/\n"
         << '\n' << ilabel << ':';
    {
        lpt::autoindent_guard indent(_out);
    
        _out << "\ncurrentState = newState;";
        if (  s._config.count(keyword::noInboundEvents) 
           || s._transitions.empty()
        ) {
            _out << "\nnoChannel = true;";
        }
    
        _out << '\n';

        visit_activity(keyword::precondition, s);
        visit_activity(keyword::entry, s);
    }

    _out << "\n\n" << blabel << ':';
    if (s._initial || s._final) {
        _out << "\n" << llabel << ':';
    }
    if (s._config.count(keyword::progressTag)) {
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
             << "\n    evtRecv.evId = " << event(upml::keyword::NullEvent) << ";"
             ;
        _out << "\nfi\n\n";
        
        //if (s._transitions.empty()) {
        //    _out << "\n/* state " << idxCrtState << " has no transitions */\n";
        //    return;
        //}
        visit_transitions(s, rd);
        visit_activity(keyword::postcondition, s);
    }

    _out << "\n/*]state " << idxCrtState << "*/\n";
}

void PseudoVisitor::visit_state_regions(const upml::sm::state& s) const
{
    for (const auto& [k, r] : s._regions) {
        visit_region(*r, s._id);
    }
}

void PseudoVisitor::visit_activity(
    const upml::sm::state&    s,
    const upml::sm::activity& a) const
{
    _out << "\n//" << a << '\n';
    auto itB(a._args.begin());
    do {
        auto itE(std::find(itB, a._args.end(), upml::keyword::stmtSep));
        upml::sm::activity astmt = {
            ._id       = a._id,
            ._state    = idx(state(s._id)),
            ._activity = a._activity,
            ._args     = upml::sm::activity::args(itB, itE)
        };
        if ( ! astmt._args.size() ) {
            std::cerr << "Warning: activity with no args:\n"<< astmt << "\n";
        }

        if (keyword::send == astmt._args[upml::sm::activity::_argOrder::aoActivity]) {
            assert(keyword::send == astmt._args[upml::sm::activity::_argOrder::aoActivity]);
            const auto toSt(scoped_name::create(astmt._args[upml::sm::activity::_argOrder::aoState]));
            assert(toSt._scope == keyword::state);
            const auto destRegPtr(_sm.owner_region(toSt._name));
            assert(destRegPtr);
            const auto evt(scoped_name::create(astmt._args[upml::sm::activity::_argOrder::aoEvent]));
            assert(evt._scope == keyword::event);

            const auto& destStatePtr(_sm.state(toSt._name));
            assert(destStatePtr != nullptr); // unless someone made a typo
            if ( ! destStatePtr->_regions.empty()) {
                for (const auto& [k, destRegPtr] : destStatePtr->_regions) {
                    _out << "send_event(" << idx(region(destRegPtr->_id))
                        << ", " << event(evt._name)
                        << ", " << astmt._state
                        << ", " << idx(state(toSt._name))
                        << "); \n";
                }
            } else {
                // simple leaf state
                _out << "send_event(" << idx(region(destStatePtr->_ownedByRegion->_id))
                    << ", " << event(evt._name)
                    << ", " << astmt._state
                    << ", " << idx(state(toSt._name))
                    << "); \n";
            }
        } else if (keyword::trace == astmt._args[upml::sm::activity::_argOrder::aoActivity]) {
            _out << "printf(\"";
            std::ranges::copy(astmt._args.begin()+1, 
                              astmt._args.end(),
                              std::ostream_iterator<upml::sm::activity::args::value_type>(_out, " "));
            _out << "\\n\"); \n";
        } else if (  astmt._activity == keyword::precondition
                  || astmt._activity == keyword::postcondition
                  ) {
            _out << "assert(";
            for (const auto& tok: astmt._args) {
                _out << token(tok);
            }
            _out << ");\n";
        } else {
            std::ranges::for_each(astmt._args.begin(), astmt._args.end(),
                                  [self=this](auto&& tok){ self->_out << self->token(tok) << ' '; });
            _out << ";\n";
        }

        itB = itE == a._args.end() ?  itE : itE + 1/*;*/;
    } while(itB != a._args.end());
}

std::string PseudoVisitor::token(const std::string& tok) const
{
    static const std::map<std::string, std::string> spinTokens{
    };

    const auto ttok(scoped_name::create(tok));
    if ( ! ttok._item.empty() && ttok._scope == keyword::state) {
        const auto& destStatePtr(_sm.state(ttok._name));
        assert(destStatePtr != nullptr);
        assert(destStatePtr->_regions.size() == 1); // TODO: syntax error if multiple regions
        for (const auto& [k, destRegPtr] : destStatePtr->_regions) {
            return region(destRegPtr->_id) + ttok._itemType/*:*/ + ttok._item + ' ';
        }
        assert(false);
    }
    else {
        auto umlTok(ttok.to_string());
        boost::algorithm::trim(umlTok);
        const auto it(spinTokens.find(umlTok));
        return it != spinTokens.end() ? it->second : umlTok;
    }

    assert(false);
    return tok;
}

void PseudoVisitor::visit_guard(
    const upml::sm::state&      s,
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

void PseudoVisitor::visit_effect(
    const upml::sm::state&      s,
    const upml::sm::transition& t) const
{
    if (t._effect.empty()) {
        return;
    }

    // TODO: loop over individual statements
    std::span stmt(t._effect.begin(), t._effect.end());
    upml::sm::activity a = {
        ._id       = upml::sm::tag(upml::sm::activity::_tag, t._line),
        ._state    = idx(state(s._id)),
        ._activity = stmt[0],
        ._args     = upml::sm::activity::args(stmt.begin(), stmt.end())
    };
    // TODO: UML transition semanic: 
    // - exit old state
    // - generate effect/execute action associated with transition
    // - enter new state
    // unless new state == old state:
    // - self-transitions (exit & enter again) not supported; implemented as internal
    //_out << "currentState = idx_unknown; "; 
    visit_activity( s, a);
}

void PseudoVisitor::visit_transition(
    const upml::sm::state&      s,
    const upml::sm::transition& t) const
{
    const auto evt(scoped_name::create(t._event));
    const auto toSt(scoped_name::create(t._toState));
    const auto idxCrtState(idx(state(s._id)));

    lpt::autoindent_guard indent(_out);

    _out << "\n//" << t << '\n';
    _out << ":: (evtRecv.evId == " << event(evt._name); 
         visit_guard(s, t);
    _out << ") -> ";
         visit_effect(s, t);
    if (idx(state(toSt._name)) == idxCrtState) {
        visit_activity(keyword::postcondition, s);
        //lpt::autoindent_guard indent(_out);
        _out << "\nnewState = " << idx(state(toSt._name)) << "; ";
        _out << "\ngoto " << name("body", s._id) << ';';
    } else {
        visit_activity(keyword::exit, s);
        visit_activity(keyword::postcondition, s);
        //lpt::autoindent_guard indent(_out);
        _out << "\nnewState = " << idx(state(toSt._name)) << "; ";
        _out << "\ngoto " << name(keyword::entry, toSt._name) << ';';
    }
    _out << "\n";
}

void PseudoVisitor::visit_transitions(const upml::sm::state& s, const RegionData& rd) const
{
    const int myIdx(_states.find(s._id)->second);
    const auto idxCrtState(idx(state(s._id)));

    if ( ! s._transitions.empty()) {
        _out << "\n/* transitions " << idxCrtState << "[*/"
             << "\nif\n";
        for (const auto& [k, t] : s._transitions) {
           visit_transition(s, t);
        }
        visit_activity(keyword::timeout, s);
        //TODO: resend unhandled events to the hierarchical parent state
        _out << "\nfi"
             << "\n/*]transitions " << idxCrtState << "*/\n"
             ;
    }

    visit_activity(keyword::postcondition, s);
}

void PseudoVisitor::visit_activity(
    const std::string&         activityType,
    const upml::sm::state&     s) const
{
    const int myIdx(_states.find(s._id)->second);
    const auto idxCrtState(idx(state(s._id)));

    if ( ! s._activities.empty()) {
        for (const auto& a : s._activities) {
            if ( ! a._args.size() ) {
                std::cerr << "Warning: activity with no args:\n"<< a << "\n";
                continue;
            }
            if (a._activity == activityType) {
                visit_activity(s, a);
            }
        }
    }
}

void PseudoVisitor::visit_region(const upml::sm::region& r, const id_t& ownerTag) const
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
    {
        lpt::autoindent_guard indent(_out);
        for (const auto& [k, s] : r._substates) {
            visit_activity(keyword::localvar, *s);
        }
    }

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
        if (s->_final && ! s->_initial) { // initial might be the final too
            assert(idx(state(k)) == regionData._finalState);
            visit_state(*s, regionData);
            break;  //only one such (supposedly)
        }
    }

    _out << "\n} // " << rname << ' ' << ownerTag << "\n";


    for (const auto& [k, s] : r._substates) {
        visit_state_regions(*s);
    }
}

void PseudoVisitor::visit_activity(
    const std::string&         activityType,
    const upml::sm::state&     s,
    const ActivityProcessor_t& processor) const
{
    for (const auto& a : s._activities) {
        //std::cerr << s._id << "activity: " << a << '\n';
        if ( ! a._args.size() ) {
            continue;
        }
        if (a._activity != activityType) {
            continue;
        }
        processor(a);
    }

    for (const auto& [k1, r1] : s._regions) {
        for (const auto& [k2, s2] : r1->_substates) {
            visit_activity(activityType, *s2, processor);
        }
    }
}

void PseudoVisitor::visit_activity(
    const std::string&         activityType,
    const ActivityProcessor_t& processor) const
{
    for (const auto& [k, r] : _sm._regions) {
        //std::cerr << r->_id << '\n';
        for (const auto& [k, s] : r->_substates) {
            //std::cerr << s->_id << '\n';
            visit_activity(activityType, *s, processor);
            for (const auto& [k, r2] : s->_regions) {
                //std::cerr << r2->_id << '\n';
                for (const auto& [k, s2] : r2->_substates) {
                    visit_activity(activityType, *s2, processor);
                }
            }
        }
    }
    _out << "\n\n";
}

void PseudoVisitor::visit() const
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
    _out << "\n\nchan _channels[" << _regions.size() << "] = [" << _regions.size() << "] of {event}; \n";
    for (const auto& [k, r] : _sm._regions) {
        for (const auto& [k2, s2] : r->_substates) {
            visit_activity(keyword::globalvar, *s2);
        }
    }

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
            for (const auto& [k2, s2] : r->_substates) {
                visit_activity(keyword::invariant, *s2, 
                              [self=this](const upml::sm::activity& a){
                                    self->_out << "\n//" << a << '\n';
                                    self->_out << ":: atomic { !(";
                                    for (const auto& tok: a._args) {
                                        self->_out << self->token(tok);
                                    }
                                    self->_out << ") -> assert(";
                                    for (const auto& tok: a._args) {
                                        self->_out << self->token(tok);
                                    }
                                    self->_out << ") };\n";
                              });
            }
        }
        _out << "\nod";
    }
    _out << "\n} // invariants\n\n";

    _out << "\ninit {\n"
        << "    atomic {\n";
    for (const auto& [k, r] : _regions) {
        _out << "        run " << region(k) << "(); \n";
    }
    _out <<     "        run invariants(); \n";
    _out <<     "    }\n";
    _out <<     "    //(_nr_pr == 1); \n";

    _out <<     "} // init\n\n";

    // LTLs are model-wide but plantuml forces ltl inside a state as an activity.
    // Any state would do but for now assume only the closed environment/top ones have ltl clauses
    _out << "\n// ltl claims: run with spin -ltl xyz or spin -noclaim \n";
    visit_activity(keyword::ltl,
                   [self=this](const upml::sm::activity& a){
                        self->_out << "//" << a << '\n';
                        self->_out << "ltl ";
                        for (const auto& tok: a._args) {
                            auto item(self->token(tok));
                            self->_out << item << ' ';
                        }
                        self->_out << ";\n ";
                   });

    visit_activity(keyword::chanltl,
                   [self=this](const upml::sm::activity& a){
                        self->_out << "//" << a << '\n';
                        self->_out << "trace { do :: ";
                        for (const auto& tok: a._args) {
                            auto ttok(scoped_name::create(tok));
                            auto item(ttok._scope == keyword::event ? event(ttok._name) : self->token(tok));
                            self->_out << item << ' ';
                        }
                        self->_out << " od; }\n ";
                   });
    visit_activity(keyword::nochanltl,
                   [self=this](const upml::sm::activity& a){
                        self->_out << "//" << a << '\n';
                        self->_out << "notrace { do :: ";
                        for (const auto& tok: a._args) {
                            auto ttok(scoped_name::create(tok));
                            auto item(ttok._scope == keyword::event ? event(ttok._name) : self->token(tok));
                            self->_out << item << ' ';
                        }
                        self->_out << " od; }\n ";
                   });

    _out <<     "/*UPML end*/\n\n";
}

bool generate(
    std::ostream&            out,
    upml::sm::state_machine& sm)
{
    spin::fsm::PseudoVisitor psm(sm, out);
    psm.visit();
    return true;
}

} // spin::fsm

} //namespace upml

