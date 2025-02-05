/*
 *  $Id: $
 *
 *  Copyright 2025 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 */

#ifndef INCLUDED_switch_state_machine_hpp_61975fb7_3a37_4eea_b735_720b4a43da3c
#define INCLUDED_switch_state_machine_hpp_61975fb7_3a37_4eea_b735_720b4a43da3c

#pragma once

#include <iostream>
#include <boost/msm/back/state_machine.hpp>
 
#include <boost/msm/front/state_machine_def.hpp>
#include <boost/msm/front/functor_row.hpp>

namespace {

    namespace msm  = boost::msm;
    namespace msmf = boost::msm::front;
    namespace mpl  = boost::mpl;

    // ----- Events
    struct LampSwitch {};
    struct WallSwitch {};

    // ----- State machine
    struct SwitchStateMachine : msmf::state_machine_def<SwitchStateMachine>
    {
        bool _lightOn{false};
	
        // States
        struct LightOn : msmf::state<>
        {
            // Entry action
            template <class Event,class Fsm>
            void on_entry(Event const&, Fsm& fsm) const {
                std::cout << "LightOn::on_entry()" << std::endl;
		fsm._lightOn = true;
            }
            // Exit action
            template <class Event,class Fsm>
            void on_exit(Event const&, Fsm& fsm) const {
                std::cout << "LightOn::on_exit()" << std::endl;
		fsm._lightOn = false;
            }
        };

        struct BothOff : msmf::state<> {};
        struct WallOff : msmf::state<> {};
        struct LampOff : msmf::state<> {};

        // Set initial state
        typedef BothOff initial_state;

        // Transition table
        struct transition_table:mpl::vector<
            //          Start    Event       Next      Action       Guard
            msmf::Row < BothOff, LampSwitch, WallOff,  msmf::none,  msmf::none >
          , msmf::Row < BothOff, WallSwitch, LampOff,  msmf::none,  msmf::none >
          , msmf::Row < WallOff, LampSwitch, BothOff,  msmf::none,  msmf::none >
          , msmf::Row < WallOff, WallSwitch, LightOn,  msmf::none,  msmf::none >
          , msmf::Row < LightOn, LampSwitch, WallOff,  msmf::none,  msmf::none >
          , msmf::Row < LightOn, WallSwitch, LampOff,  msmf::none,  msmf::none >
          , msmf::Row < LampOff, LampSwitch, LightOn,  msmf::none,  msmf::none >
          , msmf::Row < LampOff, WallSwitch, BothOff,  msmf::none,  msmf::none >
        > {};
    };

    // Pick a back-end
    typedef msm::back::state_machine<SwitchStateMachine> Switch;

} // namespace


#endif //#define INCLUDED_switch_state_machine_hpp_61975fb7_3a37_4eea_b735_720b4a43da3c
