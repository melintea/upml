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
    void visit_state_regions(const upml::sm::state& s) const;
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

void Visitor::visit_state_regions(const upml::sm::state& s) const
{
    for (const auto& [k, r] : s._regions) {
        visit_region(r, s._id);
    }
}

void Visitor::visit_region(const upml::sm::region& r, const id_t& ownerTag) const
{
    RegionData regionData;
    regionData._id        = r._id;
    regionData._regionIdx = _regions.find(r._id)->second; // TODO: this is always 1 - wrong
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

    _out << "\n\nfair+ process (" << rname << " \\in {" << idx(rname) << "}) \\* " << ownerTag
         << "\n{"
         ;

    //TODO

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

    _out << "\nidx_unknown = -1\n";
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
    assert(from >= idx_proc_Min /\ from <= idx_proc_Max);
    assert(to >= idx_proc_Min /\ to <= idx_proc_Max);
    assert(evt >= idx_event_Min /\ evt <= idx_event_Max);
    channels[to] := Append(@, evt);
}
macro recv_event(evt, to) {
    assert(to >= idx_proc_Min /\ to <= idx_proc_Max);
    await Len(channels[to]) > 0;
    evt := Head(channels[to]);
    print <<"P:", to, "<-i", evt>>;
    assert(evt >= idx_event_Min /\ evt <= idx_event_Max);
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

