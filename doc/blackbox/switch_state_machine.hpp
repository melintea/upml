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

#include <boost/msm/back/state_machine.hpp>
 
#include <boost/msm/front/state_machine_def.hpp>
#include <boost/msm/front/functor_row.hpp>

#include <iostream>

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
            template <class Event,class Fsm>
            void on_entry(Event const&, Fsm& fsm) const {
                std::cout << "LightOn::on_entry()" << std::endl;
		fsm._lightOn = true;
            }
            template <class Event,class Fsm>
            void on_exit(Event const&, Fsm& fsm) const {
                std::cout << "LightOn::on_exit()" << std::endl;
		fsm._lightOn = false;
            }
        };

        struct BothOff : msmf::state<> 
	{
            template <class Event,class Fsm>
            void on_entry(Event const&, Fsm& fsm) const {
                std::cout << "BothOff::on_entry()" << std::endl;
            }
            template <class Event,class Fsm>
            void on_exit(Event const&, Fsm& fsm) const {
                std::cout << "BothOff::on_exit()" << std::endl;
            }
	};
	
        struct WallOff : msmf::state<> 
	{
            template <class Event,class Fsm>
            void on_entry(Event const&, Fsm& fsm) const {
                std::cout << "WallOff::on_entry()" << std::endl;
            }
            template <class Event,class Fsm>
            void on_exit(Event const&, Fsm& fsm) const {
                std::cout << "WallOff::on_exit()" << std::endl;
            }
	};
	
        struct LampOff : msmf::state<> 
	{
            template <class Event,class Fsm>
            void on_entry(Event const&, Fsm& fsm) const {
                std::cout << "LampOff::on_entry()" << std::endl;
            }
            template <class Event,class Fsm>
            void on_exit(Event const&, Fsm& fsm) const {
                std::cout << "LampOff::on_exit()" << std::endl;
            }
	};

        // Set initial state
        typedef BothOff initial_state;

        // Transition table
#if 0
	/* For switch.error.plantuml/png */
        struct transition_table : mpl::vector<
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
#endif
#if 1
	/* Good: for switch.plantuml/png */
        struct transition_table : mpl::vector<
            //          Start    Event       Next      Action       Guard
            msmf::Row < BothOff, LampSwitch, WallOff,  msmf::none,  msmf::none >
          , msmf::Row < BothOff, WallSwitch, LampOff,  msmf::none,  msmf::none >
          , msmf::Row < WallOff, LampSwitch, BothOff,  msmf::none,  msmf::none >
          , msmf::Row < WallOff, WallSwitch, LightOn,  msmf::none,  msmf::none >
          , msmf::Row < LightOn, LampSwitch, LampOff,  msmf::none,  msmf::none >
          , msmf::Row < LightOn, WallSwitch, WallOff,  msmf::none,  msmf::none >
          , msmf::Row < LampOff, LampSwitch, LightOn,  msmf::none,  msmf::none >
          , msmf::Row < LampOff, WallSwitch, BothOff,  msmf::none,  msmf::none >
        > {};
#endif
    };

    // Pick a back-end
    typedef msm::back::state_machine<SwitchStateMachine> Switch;

} // namespace


#endif //#define INCLUDED_switch_state_machine_hpp_61975fb7_3a37_4eea_b735_720b4a43da3c
