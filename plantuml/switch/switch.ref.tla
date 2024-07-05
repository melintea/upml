/*
Model for the double switch: https://learntla.com/topics/state-machines.html
*/

---- MODULE switch ----

EXTENDS TLC, Integers, Sequences

(* constants disguised as vars *)
idx_state_Min == 0 
idx_state_BothOff == 0
idx_state_LampOff == 1
idx_state_WallOff == 2
idx_state_On == 3
idx_state_Unknown == 4
idx_state_Max == 4

idx_event_Min == 0 
idx_event_LampSwitch == 0
idx_event_WallSwitch == 1
idx_event_Unknown == 2
idx_event_Max == 2

Event == [ evtId : {idx_event_Min..idx_event_Max}, 
           fromState : {idx_state_Min..idx_state_Max}, (*sender*)
           toState : {0..100}
         ]

(**********************************************************************

--algorithm lamp {
variables   
    
    eventSink_Switch = << >>;
    
    v1 \in {1..1000};
    v2 \in {1, 2, 3};

fair process (Switch = 100)
variables
    state \in {"BothOff", "WallOff", "LampOff", "On"};
    initialState = "BothOff";
    finalState  = "On";
    currentState \in {idx_state_Min..idx_state_Max};
{
  ProcBody:
    state := "BothOff";
    currentState := idx_state_Unknown;
    v1 := 2;
    v2 := 3;
    
  EntryBothOff:
    skip;
  BodyBothOff:
    either {
        await (/\ state = initialState /\ v1 = 3); \* <== dead !!
        print <<"Moving to WallOff", v1>>;
        state := "WallOff";
        assert(TRUE);
        goto BodyWallOff;
    } or {
        await (/\ state = initialState);
        print <<"Moving to LampOff", v1>>;
        state := "LampOff";
        goto BodyLampOff;
    };
    
  BodyLampOff:
    either {
        await state = "LampOff";
        state := "BothOff";
        goto BodyBothOff;
    } or {
        await state = "LampOff";
        state := "On";
        goto BodyOn;
    };
    
  BodyWallOff:
    either {
        await state = "WallOff";
        state := "BothOff";
        goto BodyBothOff;
    } or {
        await state = "WallOff";
        state := "On";    
        goto BodyOn;
    };
    
  BodyOn:
    either {
        await state = "On";
        state := "LampOff";
        goto BodyLampOff;
    } or {
        await state = "On";
        state := "WallOff";
        goto BodyWallOff;    
    };
    
} \* Switch

fair process (ClosedEnv = 200)
{
  ProcBody:
    skip;
} \* ClosedEnv

} \* algorithm lamp

*******************************************************************)

\* BEGIN TRANSLATION (chksum(pcal) = "dac4fe92" /\ chksum(tla) = "2e5e18e4")
\* Label ProcBody of process Switch at line 47 col 5 changed to ProcBody_
VARIABLES eventSink_Switch, v1, v2, pc, state, initialState, finalState, 
          currentState

vars == << eventSink_Switch, v1, v2, pc, state, initialState, finalState, 
           currentState >>

ProcSet == {100} \cup {200}

Init == (* Global variables *)
        /\ eventSink_Switch = << >>
        /\ v1 \in {1..1000}
        /\ v2 \in {1, 2, 3}
        (* Process Switch *)
        /\ state \in {"BothOff", "WallOff", "LampOff", "On"}
        /\ initialState = "BothOff"
        /\ finalState = "On"
        /\ currentState \in {idx_state_Min..idx_state_Max}
        /\ pc = [self \in ProcSet |-> CASE self = 100 -> "ProcBody_"
                                        [] self = 200 -> "ProcBody"]

ProcBody_ == /\ pc[100] = "ProcBody_"
             /\ state' = "BothOff"
             /\ currentState' = idx_state_Unknown
             /\ v1' = 2
             /\ v2' = 3
             /\ pc' = [pc EXCEPT ![100] = "EntryBothOff"]
             /\ UNCHANGED << eventSink_Switch, initialState, finalState >>

EntryBothOff == /\ pc[100] = "EntryBothOff"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![100] = "BodyBothOff"]
                /\ UNCHANGED << eventSink_Switch, v1, v2, state, initialState, 
                                finalState, currentState >>

BodyBothOff == /\ pc[100] = "BodyBothOff"
               /\ \/ /\ (/\ state = initialState /\ v1 = 3)
                     /\ PrintT(<<"Moving to WallOff", v1>>)
                     /\ state' = "WallOff"
                     /\ Assert((TRUE), 
                               "Failure of assertion at line 59, column 9.")
                     /\ pc' = [pc EXCEPT ![100] = "BodyWallOff"]
                  \/ /\ (/\ state = initialState)
                     /\ PrintT(<<"Moving to LampOff", v1>>)
                     /\ state' = "LampOff"
                     /\ pc' = [pc EXCEPT ![100] = "BodyLampOff"]
               /\ UNCHANGED << eventSink_Switch, v1, v2, initialState, 
                               finalState, currentState >>

BodyLampOff == /\ pc[100] = "BodyLampOff"
               /\ \/ /\ state = "LampOff"
                     /\ state' = "BothOff"
                     /\ pc' = [pc EXCEPT ![100] = "BodyBothOff"]
                  \/ /\ state = "LampOff"
                     /\ state' = "On"
                     /\ pc' = [pc EXCEPT ![100] = "BodyOn"]
               /\ UNCHANGED << eventSink_Switch, v1, v2, initialState, 
                               finalState, currentState >>

BodyWallOff == /\ pc[100] = "BodyWallOff"
               /\ \/ /\ state = "WallOff"
                     /\ state' = "BothOff"
                     /\ pc' = [pc EXCEPT ![100] = "BodyBothOff"]
                  \/ /\ state = "WallOff"
                     /\ state' = "On"
                     /\ pc' = [pc EXCEPT ![100] = "BodyOn"]
               /\ UNCHANGED << eventSink_Switch, v1, v2, initialState, 
                               finalState, currentState >>

BodyOn == /\ pc[100] = "BodyOn"
          /\ \/ /\ state = "On"
                /\ state' = "LampOff"
                /\ pc' = [pc EXCEPT ![100] = "BodyLampOff"]
             \/ /\ state = "On"
                /\ state' = "WallOff"
                /\ pc' = [pc EXCEPT ![100] = "BodyWallOff"]
          /\ UNCHANGED << eventSink_Switch, v1, v2, initialState, finalState, 
                          currentState >>

Switch == ProcBody_ \/ EntryBothOff \/ BodyBothOff \/ BodyLampOff
             \/ BodyWallOff \/ BodyOn

ProcBody == /\ pc[200] = "ProcBody"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![200] = "Done"]
            /\ UNCHANGED << eventSink_Switch, v1, v2, state, initialState, 
                            finalState, currentState >>

ClosedEnv == ProcBody

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Switch \/ ClosedEnv
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Switch)
        /\ WF_vars(ClosedEnv)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
