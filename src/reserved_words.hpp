/*
 *  $Id: $
 *
 *  Copyright 2025 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 */

#ifndef INCLUDED_reserved_words_hpp_0fc98e70_5b6e_4dd4_bae1_88902fedaadb
#define INCLUDED_reserved_words_hpp_0fc98e70_5b6e_4dd4_bae1_88902fedaadb

#pragma once

namespace upml::keyword {

/*
 * Additions to the plantuml vocabulary
 */

// Reserved events
inline constexpr const char* NullEvent  = "NullEvent";
inline constexpr const char* EnterState = "EnterState";
inline constexpr const char* ExitState  = "ExitState";

// State:stuff
inline constexpr const char* entry   = "entry";
inline constexpr const char* exit    = "exit";
inline constexpr const char* precondition   = "precondition";
inline constexpr const char* postcondition  = "postcondition";
inline constexpr const char* invariant      = "invariant";
inline constexpr const char* config  = "config";
inline constexpr const char*   noInboundEvents  = "noInboundEvents";
inline constexpr const char*   progressTag      = "progressTag";
inline constexpr const char* ltl     = "ltl"; // actually this is at model/global level
inline constexpr const char* timeout = "timeout"; //TODO

// Actions
inline constexpr const char* send   = "send";
inline constexpr const char* trace  = "trace";

// scope:name
inline constexpr const char* event  = "event";
inline constexpr const char* state  = "state";


} //namespace upml::keyword


#endif //#define INCLUDED_reserved_words_hpp_0fc98e70_5b6e_4dd4_bae1_88902fedaadb
