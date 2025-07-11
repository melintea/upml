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

namespace spin::hsm {

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
    idx_t i(1); // reserve 0 for unknown
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
    std::vector<int>  _chanMap; // index of the channel in the channel array for any given state

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
    void visit_region(const upml::sm::region& r) const;
    void visit_state(const upml::sm::state& sbrk) const;
    void visit_transitions(const upml::sm::state& s) const;
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

    // Index in the chan arrays for a given state
    int  channel_idx(const upml::sm::state& s) const;
    int  channel_idx(const id_t& sn) const;
}; // PseudoVisitor

PseudoVisitor::PseudoVisitor(upml::sm::state_machine& sm,
                 std::ostream&            out)
    : _sm(sm)
    , _out(out)
{
    _events  = names("", sm.events());

    _regions = names("", sm.regions(true));
    _states  = names("", sm.states(true));

    _chanMap.reserve(_states.size() + 1);
    for (int i = 0; i < _chanMap.capacity(); ++i) {
        _chanMap.push_back(0); // Note: -1 chokes spin (!)
    }
    for (int idxc = 0; const auto& [kr, r] : _sm._regions) {
        //const auto idxr = _regions.at(name("", kr));
        const auto snames(r->states(true/*recursive*/));
        for (const auto& sn : snames) {
            const auto idxs = _states.at(name("", sn));
            _chanMap[idxs] = idxc;
        }
        ++idxc;
    }
}

int  PseudoVisitor::channel_idx(const upml::sm::state& s) const
{
    return channel_idx(s._id);
}

int  PseudoVisitor::channel_idx(const id_t& sn) const
{
    const auto idxs = _states.at(name("", sn));
    return _chanMap[idxs];
}

void PseudoVisitor::visit_state(const upml::sm::state& s) const
{
    for (const auto& [k, r] : s._regions) {
        visit_region(*r);
    }

    const int myIdx(_states.find(s._id)->second);
    const auto idxCrtState(idx(state(s._id)));
    const id_t ilabel(name(keyword::entry, s._id));
    const id_t xlabel(name(keyword::exit, s._id));
    const id_t elabel(name("end", s._id));
    const id_t blabel(name("body", s._id));
    const id_t llabel(name("loop", s._id));
    const id_t plabel(name("progress", s._id)); //TODO:non-progress cycles
    const bool topState(s._superState && !s._superState->_superState);
    const bool leafState = [&s]() {
        return s._regions.empty() || s.states(true/*recursive*/).size() == 1;
    }();

    _out << "\n/*\n" << s << "\n*/";
    _out << "\nproctype "  << s._id << "(chan superChannel; chan eventProcessedChan) \n{";
    _out << "\n    local event evtRecv;";
    _out << "\n    local eventStatus eventProcessed;";
    if ( ! leafState) {
        for (const auto& [k1, r1] : s._regions) {
            auto subchan = "substateChannel_" + k1;
            _out << "\n    chan " << subchan << " = [1] of {event};";
        }
        _out << "\n    chan substateEventProcessedChan = [1] of {eventStatus};";
    }

    _out << "\n\n" << ilabel << ":\n";
    {
        lpt::autoindent_guard indent(_out);
        _out << "\n_initialState[" << idxCrtState << "] = " << s._initial << ";";
        visit_activity(keyword::precondition, s);
        visit_activity(keyword::entry, s);
        for (const auto& [k1, r1] : s._regions) {
            for (const auto& [k2, s2] : r1->_substates) {
                if (s2->_initial) {
                    _out << "\nsend_internal_event(" << event(keyword::EnterState) 
                         << ", " << idxCrtState 
                         << ", " << idx(state(s2->_id)) 
                         << ");";
                }
            }
        }
        _out << "\n_currentState[" << idxCrtState << "] = true;";
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
        if (topState) {
            _out << "\nif";
            _out << "\n:: nempty(_internalEvents[" << channel_idx(s) << "]) -> _internalEvents[" << channel_idx(s) << "]?evtRecv;";
            _out << "\n:: initialized && empty(_internalEvents[" << channel_idx(s) << "])  -> " << elabel << ": superChannel?evtRecv;";
            _out << "\nfi";
            _out << "\nprintf(\"MSC: > " <<  s._id << " event %e in state %d\\n\", evtRecv.evId, " << idxCrtState << ");\n";
        } else {
            _out << "\n" << elabel << ": superChannel?evtRecv;";
            _out << "\nprintf(\"MSC: > " <<  s._id << " event %e in state %d\\n\", evtRecv.evId, " << idxCrtState << ");\n";
        }

        // enter/exit events
        _out << "\nif";
        _out << "\n:: (evtRecv.evId == " << event(keyword::EnterState) << " && evtRecv.toState == " << idxCrtState << ") -> ";
        _out << "\n   eventProcessedChan!" << event(keyword::EnterState) << "(idx_statusProcessed);";
        _out << "\n   goto " << blabel << "; \n";
        _out << "\n:: (evtRecv.evId == " << event(keyword::ExitState) << " && (evtRecv.toState == " << idxCrtState << " || evtRecv.toState == idx_unknown)) -> ";
        _out << "\n   goto " << xlabel << "; \n";
        for (const auto& [k1, r1] : s._regions) {
            auto subchan = "substateChannel_" + k1;
            for (const auto& [k2, s2] : r1->_substates) {
                _out << "\n:: (evtRecv.evId == " << event(keyword::EnterState) << " && evtRecv.toState == " << idx(state(s2->_id)) << ") -> ";
                _out << "\n   run " << s2->_id << "(" << subchan << ", substateEventProcessedChan);";
                _out << "\n   _currentState[" << idx(state(s2->_id)) << "] == true;";
                if ( ! topState) {
                    _out << "\n   eventProcessedChan!" << event(keyword::EnterState) << "(idx_statusProcessed);";
                }
                _out << "\n   goto " << blabel << ";";
            }
        }
        _out << "\n:: else -> skip; // send to substates for processing";
        _out << "\nfi\n";

        _out << "\n// send event to substates, check if processed";
        if ( ! leafState) {
            for (const auto& [k1, r1] : s._regions) {
                auto subchan = "substateChannel_" + k1;
                _out << "\neventProcessed.status = idx_unknown;";
                _out << "\n" << subchan << "!evtRecv;";
                _out << "\nsubstateEventProcessedChan?eventProcessed;";
                _out << "\nassert(eventProcessed.evId == evtRecv.evId);";
                _out << "\nif";
                _out << "\n:: (eventProcessed.status == idx_statusProcessed) -> ";
                if ( ! topState) { // ack all events
                    _out << "\n   eventProcessedChan!eventProcessed;";
                } else { // ack only external events
                    _out << "\n   if";
                    _out << "\n   :: (evtRecv.evId == event_EnterState || evtRecv.evId == event_ExitState) -> ";
                    _out << "\n      skip;";
                    _out << "\n   :: else -> eventProcessedChan!eventProcessed;";
                    _out << "\n   fi";
                }
                _out << "\n   goto " << blabel << ";";
                _out << "\n:: else -> assert(eventProcessed.status == idx_statusNotProcessed); skip;";
                _out << "\nfi\n";
            }
        }

        _out << "\n// transitions";
        if ( ! s._transitions.empty()) {
            _out << "\natomic {\neventProcessed.status = idx_unknown;\n";

            visit_transitions(s);
            visit_activity(keyword::postcondition, s);
            _out << "\n} // atomic";
        } else {
            _out << "\neventProcessedChan!evtRecv.evId(idx_statusNotProcessed);";
            _out << "\ngoto " << blabel << ";";
        }
    }

    _out << "\n\n" << xlabel << ':';
    {
        lpt::autoindent_guard indent(_out);
        if ( ! leafState) {
            for (const auto& [k1, r1] : s._regions) {
                auto subchan = "substateChannel_" + k1;
                _out << "\neventProcessed.status = idx_unknown;";
                _out << "\n" << subchan << "!" << event(keyword::ExitState) << "(idx_unknown, idx_unknown);";
                _out << "\nsubstateEventProcessedChan?eventProcessed;";
                _out << "\nassert(eventProcessed.status == idx_statusProcessed);\n";
            }
        }
        visit_activity(keyword::exit, s);
        visit_activity(keyword::postcondition, s);
        if ( ! topState) {
            _out << "\neventProcessedChan!" << event(keyword::ExitState) << "(idx_statusProcessed);";
        }
        _out << "\n_currentState[" << idxCrtState << "] = false;";
    }
    _out << "\n} // "  << s._id << "\n\n";
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
                    _out << "send_event(" 
                        << event(evt._name)
                        << ", " << astmt._state // from
                        << ", " << idx(state(toSt._name))
                        << "); \n";
                }
            } else {
                // simple leaf state
                _out << "send_event(" 
                    << event(evt._name)
                    << ", " << astmt._state // from
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
    auto umlTok(ttok.to_string());
    boost::algorithm::trim(umlTok);
    const auto it(spinTokens.find(umlTok));
    return it != spinTokens.end() ? it->second : umlTok;
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
    visit_activity( s, a);
}

void PseudoVisitor::visit_transition(
    const upml::sm::state&      s,
    const upml::sm::transition& t) const
{
    const auto evt(scoped_name::create(t._event));
    const auto toSt(scoped_name::create(t._toState));
    const auto idxCrtState(idx(state(s._id)));
    const id_t elabel(name("end", s._id));
    const id_t blabel(name("body", s._id));
    const id_t llabel(name("loop", s._id));
    const id_t plabel(name("progress", s._id)); //TODO:non-progress cycles

    lpt::autoindent_guard indent(_out);

    _out << "\n//" << t << '\n';
    _out << ":: (evtRecv.evId == " << event(evt._name); 
    visit_guard(s, t);
    _out << ") -> ";
    visit_effect(s, t);

    if (idx(state(toSt._name)) == idxCrtState) {
        // Should be an exit&re-enter transition, not an internal one
        // but process as internal
        // TODO: distinguish between the two
        visit_activity(keyword::postcondition, s);
        _out << "\ngoto " << blabel << ';'; // remain in state
    } else {
        auto lcaPath(_sm.transition(_sm.state(s._id), _sm.state(toSt._name)));
        _out << "\n// " << lcaPath;
        /*
        std::ranges::for_each(std::as_const(lcaPath._exitStates), 
            [self=this, &idxCrtState](const auto& change) {
                self->_out << "\nsend_internal_event(" << event(change._event._id) 
                           << ", " << idxCrtState 
                           << ", " << idx(state(change._statePtr->_id ))  // to
                           << ");";
            });
        */
        if (lcaPath._exitStates.size()) {
            const auto& change = *lcaPath._exitStates.rbegin();
            assert(change._event._id == upml::keyword::ExitState);
            _out << "\nsend_internal_event(" << event(change._event._id) 
                 << ", " << idxCrtState 
                 << ", " << idx(state(change._statePtr->_id ))  // to
                 << ");";
        }
        std::ranges::for_each(std::as_const(lcaPath._enterStates), 
            [self=this, &idxCrtState](const auto& change) {
                self->_out << "\nsend_internal_event(" << event(change._event._id) 
                           << ", " << idxCrtState 
                           << ", " << idx(state(change._statePtr->_id ))  // to
                           << ");";
            });
        visit_activity(keyword::postcondition, s);
        _out << "\neventProcessedChan!" << event(evt._name) << "(idx_statusProcessed);";
        _out << "\ngoto " << blabel << ';'; // remain in state awaiting the Exit event
    }
    _out << "\n";
}

void PseudoVisitor::visit_transitions(const upml::sm::state& s) const
{
    const int myIdx(_states.find(s._id)->second);
    const auto idxCrtState(idx(state(s._id)));
    const id_t blabel(name("body", s._id));

    if ( ! s._transitions.empty()) {
        _out << "\n/* transitions " << idxCrtState << "[*/"
             << "\nif\n";
        for (const auto& [k, t] : s._transitions) {
           visit_transition(s, t);
        }
        visit_activity(keyword::timeout, s);
        // resend unhandled events to the hierarchical parent state
        {
            lpt::autoindent_guard indent(_out);
            _out << "\n:: else ->"
                 << "\neventProcessedChan!evtRecv.evId(idx_statusNotProcessed);"
                 << "\ngoto " << blabel << ";";
                 ;
        }
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

void PseudoVisitor::visit_region(const upml::sm::region& r) const
{
    {
        lpt::autoindent_guard indent(_out);
        for (const auto& [k, s] : r._substates) {
            visit_activity(keyword::localvar, *s);
        }
    }

    for (const auto& [k, s] : r._substates) {
        if (s->_initial) {
            //assert(idx(state(k)) == regionData._initialState);
            visit_state(*s);
            break;  //only one such (supposedly)
        }
    }

    for (const auto& [k, s] : r._substates) {
        if (s->_initial || s->_final) {
            continue;
        }
        visit_state(*s);
    }

    for (const auto& [k, s] : r._substates) {
        if (s->_final && ! s->_initial) { // initial might be the final too
            visit_state(*s);
            break;  //only one such (supposedly)
        }
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

    _out << "\n#define idx_unknown 0\n";
    _out << "\n#define idx_statusNotProcessed 0";
    _out << "\n#define idx_statusProcessed 1\n";

    for (const auto& [k, s] : _states) {
        _out << "\n#define " << idx(state(k)) << " " << s;
    }
    _out << "\n#define numStates " << _states.size() + 1 << '\n';
    _out << "\nbool _currentState[numStates]; ";
    _out << "\nbool _initialState[numStates]; \n";
    auto istates(_sm.initial_states());
    if (istates.size()) {
        _out << "\n#define initialized (true";
        for (const auto& s : istates) {
            _out << " && _initialState[" << idx(state(s)) << "]";
        }
        _out << ")";
    } else {
        _out  << "\n#define initialized (skip)";
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
    _out << "};";

    _out << "\ntypedef event {mtype evId; short toState; short fromState;};";
    _out << "\ntypedef eventStatus {mtype evId; short status;};";

    _out << "\n\nint _chanMap[numStates] = {";
    for (const char* comma = ""; const auto v : _chanMap) {
        _out << std::exchange(comma, ",") << v;
    }
    _out << "};";

    auto nTopRegs(_sm._regions.size());
    _out << "\nchan _externalEvents[" << nTopRegs << "] = [1] of {event};";
    _out << "\nchan _internalEvents[" << nTopRegs << "] = [2*" << _sm.depth() << "] of {event};\n";
    _out << "\nchan _eventProcessed[" << nTopRegs << "] = [1] of {eventStatus};";
    _out << "\n";
    
    for (const auto& [k, r] : _sm._regions) {
        for (const auto& [k2, s2] : r->_substates) {
            visit_activity(keyword::globalvar, *s2);
        }
    }

    _out << "\ninline send_internal_event(evt, fromState, toState)"
            "\n{"
            "\n    assert(nfull(_internalEvents[_chanMap[toState]]));"
            "\n    _internalEvents[_chanMap[toState]]!evt(toState, fromState);"
            "\n}\n"
            "\ninline send_event(evt, fromState, toState)"
            "\n{"
            "\n    (initialized && empty(_internalEvents[_chanMap[toState]]));"
            "\n    _externalEvents[_chanMap[toState]]!evt(toState, fromState);"
            "\n    _eventProcessed[_chanMap[toState]]?_(_);"
            "\n}\n"
            ;

    for (const auto& [k, r] : _sm._regions) {
        assert(r->_substates.size() == 1);
        assert(r->_substates.begin()->second->_initial);
        visit_state(*r->_substates.begin()->second);
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
    for (const auto& [k, r] : _sm._regions) {
        const auto idxc(channel_idx(r->_substates.begin()->second->_id));
        _out << "        run " << r->_substates.begin()->second->_id 
             << "(_externalEvents[" << idxc << "], "
             << "_eventProcessed[" << idxc << "]); \n";
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

    auto chanLtlFunc =  [self=this](const char* keyword, const upml::sm::activity& a){
        self->_out << "//" << a << '\n';
        self->_out << keyword << " { do :: \n";
        lpt::autoindent_guard indent(self->_out);
        for (auto it = a._args.begin(); it != a._args.end(); ++it) {
            const auto& tok(*it);
            auto ttok(scoped_name::create(tok));
            if (ttok._scope == keyword::event) {
                self->_out << event(ttok._name) << ' ';
            } else if (ttok._scope == keyword::state) {
                const auto& context(*std::prev(it));
                if (context == "[") { // array, presumably of channels
                    self->_out << self->channel_idx(ttok._name) << ' ';
                } else {
                    self->_out << self->token(tok) << ' ';
                }
            } else if (tok == ";") {
                self->_out << self->token(tok) << "\n";
            }  else {
                self->_out << self->token(tok) << ' ';
            }
        }
        self->_out << "od; }\n ";
    };

    visit_activity(keyword::chanltl,
                   [&chanLtlFunc](const upml::sm::activity& a){
                        chanLtlFunc("trace", a);
                   });
    visit_activity(keyword::nochanltl,
                   [&chanLtlFunc](const upml::sm::activity& a){
                        chanLtlFunc("notrace", a);
                   });

    _out <<     "/*UPML end*/\n\n";
}

bool generate(
    std::ostream&            out,
    upml::sm::state_machine& sm)
{
    spin::hsm::PseudoVisitor psm(sm, out);
    psm.visit();
    return true;
}

} // spin::hsm

} //namespace upml

