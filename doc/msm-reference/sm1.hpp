/*
 *  $Id: $
 *
 *  Copyright 2025 Aurelian Melinte.
 *  Released under GPL 3.0 or later.
 *
 */

#ifndef INCLUDED_sm1_hpp_11975fb7_3a37_4eea_b735_720b4a43da3c
#define INCLUDED_sm1_hpp_11975fb7_3a37_4eea_b735_720b4a43da3c

#pragma once

#include <boost/msm/back/state_machine.hpp>
 
#include <boost/msm/front/state_machine_def.hpp>
#include <boost/msm/front/functor_row.hpp>

#include <cassert>
#include <iostream>

namespace sm1 {

    namespace msm  = boost::msm;
    namespace msmf = boost::msm::front;
    namespace mpl  = boost::mpl;

    // ----- Events
    struct T1 { T1(){std::cout<<"--T1: ";} };
    struct T2 { T2(){std::cout<<"--T2: ";} };
    struct T3 { T3(){std::cout<<"--T3: ";} };
    struct T4 { T4(){std::cout<<"--T4: ";} };
    struct T5 { T5(){std::cout<<"--T5: ";} };
    struct T6 { T6(){std::cout<<"--T6: ";} };

    // ----- State machine
    struct SM1 : msmf::state_machine_def<SM1>
    {
    
        // States
        struct S1 : msmf::state<>
        {
            template <class Event,class Fsm>
            void on_entry(Event const&, Fsm& fsm) const {std::cout << "S1::on_entry\n";}
            template <class Event,class Fsm> 
            void on_exit(Event const&, Fsm& fsm) const {std::cout << "S1::on_exit";}
        };

        struct S2 : msmf::state<>
        {
            template <class Event,class Fsm>
            void on_entry(Event const&, Fsm& fsm) const {std::cout << "S2::on_entry\n";}
            template <class Event,class Fsm> 
            void on_exit(Event const&, Fsm& fsm) const {std::cout << "S2::on_exit";}
        };
    
        struct S3 : msmf::state<>
        {
            template <class Event,class Fsm>
            void on_entry(Event const&, Fsm& fsm) const {std::cout << "S3::on_entry\n";}
            template <class Event,class Fsm> 
            void on_exit(Event const&, Fsm& fsm) const {std::cout << "S3::on_exit()";}
        };
    
        struct CS1_ : msmf::state_machine_def<CS1_>
        {
            template <class Event,class Fsm>
            void on_entry(Event const&, Fsm& fsm) const {std::cout << "CS1::on_entry\n";}
            template <class Event,class Fsm> 
            void on_exit(Event const&, Fsm& fsm) const {std::cout << "CS1::on_exit";}
        
            //--- region 1

            struct CS1r1S1 : msmf::state<>
            {
                template <class Event,class Fsm>
                void on_entry(Event const&, Fsm& fsm) const {std::cout << "CS1r1S1::on_entry\n";}
                template <class Event,class Fsm> 
                void on_exit(Event const&, Fsm& fsm) const {std::cout << "CS1r1S1::on_exit()";}
            };
            struct CS1r1S2 : msmf::state<>
            {
                template <class Event,class Fsm>
                void on_entry(Event const&, Fsm& fsm) const {std::cout << "CS1r1S2::on_entry\n";}
                template <class Event,class Fsm> 
                void on_exit(Event const&, Fsm& fsm) const {std::cout << "CS1r1S2::on_exit()";}
            };
        
            //--- region 2
        
            struct CS1r2S1 : msmf::state<>
            {
                template <class Event,class Fsm>
                void on_entry(Event const&, Fsm& fsm) const {std::cout << "CS1r2S1::on_entry\n";}
                template <class Event,class Fsm> 
                void on_exit(Event const&, Fsm& fsm) const {std::cout << "CS1r2S1::on_exit()";}
            };
            struct CS1r2S2 : msmf::state<>
            {
                template <class Event,class Fsm>
                void on_entry(Event const&, Fsm& fsm) const {std::cout << "CS1r2S2::on_entry\n";}
                template <class Event,class Fsm> 
                void on_exit(Event const&, Fsm& fsm) const {std::cout << "CS1r2S2::on_exit()";}
            };
        
            typedef mpl::vector<CS1r1S1, CS1r2S1> initial_state;
        
            bool gtrue1(const T4&)  {return true;}
            bool gtrue2(const T4&)  {return true;}
            bool gtrue(const T4&)  {return true;}
            bool gfalse(const T4&) {return false;}
        
            void t4(const T4&) {std::cout<<" - CS1::t4 - ";}
            void t5(const T5&) {std::cout<<" - CS1::t5 - ";}
        
            struct transition_table : mpl::vector<
                //            Start    Event       Next        Action        Guard
                   // a_row < CS1r1S1  , T4        , CS1r1S2   , &CS1_::t4   /*, msmf::none*/ >
                        row < CS1r1S1  , T4        , CS1r1S2   , &CS1_::t4   , &CS1_::gtrue1 >  // defers to CS1's T4 if guard is false
                //--- region 2
                    ,   row < CS1r2S1  , T4        , CS1r2S2   , &CS1_::t4   , &CS1_::gfalse >  // conflicts with region 1 a_row if both guards evaluate to true -> asserts
                    , a_row < CS1r2S1  , T5        , CS1r2S2   , &CS1_::t5   /*, msmf::none*/ >
            > {};
        }; // CS1_
        using CS1 = msm::back::state_machine<CS1_>;
    
    
        void t1(const T1&) {std::cout<<" - SM::t1 - ";}
        void t2(const T2&) {std::cout<<" - SM::t2 - ";}
        void t3(const T3&) {std::cout<<" - SM::t3 - ";}
        void t4(const T4&) {std::cout<<" - SM::t4 - ";}

        // Set initial state
        typedef S1 initial_state;

        typedef SM1 SM;
    
        struct transition_table : mpl::vector<
            //            Start    Event       Next        Action        Guard
                  a_row < S1       , T1        , CS1       , &SM::t1      /*, msmf::none*/ >
          ,       a_row < S1       , T4        , S1        , &SM::t4      /*, msmf::none*/ >
          ,       a_row < CS1      , T2        , S2        , &SM::t2      /*, msmf::none*/ >
          ,       a_row < CS1      , T4        , CS1       , &SM::t4      /*, msmf::none*/ > //if gtrue: trumped by CS1r1S1 / CS1's table, else this runs
          ,       a_row < S2       , T3        , S3        , &SM::t3      /*, msmf::none*/ >
        > {};
    }; // SM1
    using SM = msm::back::state_machine<SM1>;

} // namespace sm1


#endif //#define INCLUDED_sm1_hpp_11975fb7_3a37_4eea_b735_720b4a43da3c
