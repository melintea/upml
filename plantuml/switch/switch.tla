/*
./upml --in ../plantuml/switch/switch.plantuml --backend tla --out ../plantuml/switch/switch.tla 
*/
/*
   Generated by UPML v0.04
   Mon Aug  5 15:33:39 2024


    (F:'';L:1;C:1)
    machine switch {
        (F:'';L:17;C:1)
        -- r17 {
            (F:'';L:17;C:1)
            state Human final:0;initial:0 {
                (F:'';L:19;C:1)
                -- r19 {
                    (F:'';L:0;C:0)
                    state Flip final:0;initial:1 {
                        (F:'';L:21;C:1) Flip --> Flip NullEvent[]/send,event:LampSwitch,to,state:Switch, (t21)
                        (F:'';L:22;C:1) Flip --> Flip NullEvent[]/send,event:WallSwitch,to,state:Switch, (t22)
                        noInboundEvents,
                    }
                }
            }
            (F:'';L:28;C:1)
            state Switch final:0;initial:0 {
                (F:'';L:30;C:1)
                -- r30 {
                    (F:'';L:0;C:0)
                    state BothOff final:0;initial:1 {
                        (F:'';L:32;C:1) BothOff --> WallOff LampSwitch[]/ (t32)
                        (F:'';L:35;C:1) BothOff --> LampOff WallSwitch[]/ (t35)
                        progressTag,
                    }
                    (F:'';L:0;C:0)
                    state LampOff final:0;initial:0 {
                        (F:'';L:36;C:1) LampOff --> BothOff WallSwitch[]/ (t36)
                        (F:'';L:43;C:1) LampOff --> On LampSwitch[]/ (t43)
                        progressTag,
                    }
                    (F:'';L:0;C:0)
                    state On final:0;initial:0 {
                        (F:'';L:40;C:1) On --> WallOff LampSwitch[]/ (t40)
                        (F:'';L:46;C:1) On --> LampOff WallSwitch[]/ (t46)
                        progressTag,
                    }
                    (F:'';L:0;C:0)
                    state WallOff final:0;initial:0 {
                        (F:'';L:33;C:1) WallOff --> BothOff LampSwitch[]/ (t33)
                        (F:'';L:39;C:1) WallOff --> On WallSwitch[]/ (t39)
                        progressTag,
                    }
                }
            }
        }
    } switch

*/

---- MODULE switch ----------------------------------------------------

EXTENDS TLC, Integers, Sequences

idx_Unknown == -1

idx_state_BothOff == 1
idx_state_Flip == 2
idx_state_Human == 3
idx_state_LampOff == 4
idx_state_On == 5
idx_state_Switch == 6
idx_state_WallOff == 7

idx_region_r17 == 1
idx_region_r19 == 2
idx_region_r30 == 3

idx_event_LampSwitch == 1
idx_event_NullEvent == 2
idx_event_WallSwitch == 3

(**********************************************************************

--algorithm switch {

variables

    procs = { idx_region_r17, idx_region_r19, idx_region_r30 };
    channels = [p \in procs |-> <<>>];
    currentState = [p \in procs |-> idx_Unknown];
    stateTransitions = { "t21", "t22", "t32", "t35", "t36", "t43", "t40", "t46", "t33", "t39" };
    visitedTransitions = [t \in stateTransitions |-> FALSE];
    maxUmlEvents = -20;  \* limit the number of UML events in the run

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
    }; 


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

    

fair+ process (region_r17 \in {idx_region_r17}) \* switch
variables
    evtRecv = idx_Unknown; 
    initialState = idx_Unknown; 
    finalState = idx_Unknown; 
    newState = initialState; 
    noChannel = FALSE; 
{
proc_body_idx_region_r17: currentState[self] := initialState;

\* state idx_state_Human[

entry_Human: skip;
    currentState[self] := newState;
    noChannel := TRUE;


body_Human: skip;
    if ( noChannel = FALSE ) {
        L1:recv_event(evtRecv, self, currentState[self]); 
    } else {
        evtRecv := idx_event_NullEvent;
    };


\*]state idx_state_Human


\* state idx_state_Switch[

entry_Switch: skip;
    currentState[self] := newState;
    noChannel := TRUE;


body_Switch: skip;
    if ( noChannel = FALSE ) {
        L2:recv_event(evtRecv, self, currentState[self]); 
    } else {
        evtRecv := idx_event_NullEvent;
    };


\*]state idx_state_Switch

} \* region_r17 switch


fair+ process (region_r19 \in {idx_region_r19}) \* Human
variables
    evtRecv = idx_Unknown; 
    initialState = idx_state_Flip; 
    finalState = idx_Unknown; 
    newState = initialState; 
    noChannel = FALSE; 
{
proc_body_idx_region_r19: currentState[self] := initialState;

\* state idx_state_Flip[

entry_Flip: skip;
    currentState[self] := newState;
    noChannel := TRUE;


body_Flip: skip;
loop_Flip: skip;
    if ( noChannel = FALSE ) {
        L3:recv_event(evtRecv, self, currentState[self]); 
    } else {
        evtRecv := idx_event_NullEvent;
    };


    \* transitions idx_state_Flip[ 
    L4:
    either {

        \*     (F:'';L:21;C:1) Flip --> Flip NullEvent[]/send,event:LampSwitch,to,state:Switch, (t21)
        await (evtRecv = idx_event_NullEvent);L5:send_event(idx_region_r30, idx_event_LampSwitch, idx_state_Flip, idx_state_Switch); 

        visitedTransitions["t21"] := TRUE;

        newState := idx_state_Flip; 
        goto body_Flip;

    } or {

        \*     (F:'';L:22;C:1) Flip --> Flip NullEvent[]/send,event:WallSwitch,to,state:Switch, (t22)
        await (evtRecv = idx_event_NullEvent);L6:send_event(idx_region_r30, idx_event_WallSwitch, idx_state_Flip, idx_state_Switch); 

        visitedTransitions["t22"] := TRUE;

        newState := idx_state_Flip; 
        goto body_Flip;

    }; \* either
    \*]transitions idx_state_Flip

\*]state idx_state_Flip

} \* region_r19 Human


fair+ process (region_r30 \in {idx_region_r30}) \* Switch
variables
    evtRecv = idx_Unknown; 
    initialState = idx_state_BothOff; 
    finalState = idx_Unknown; 
    newState = initialState; 
    noChannel = FALSE; 
{
proc_body_idx_region_r30: currentState[self] := initialState;

\* state idx_state_BothOff[

entry_BothOff: skip;
    currentState[self] := newState;


body_BothOff: skip;
loop_BothOff: skip;
progress_BothOff: skip;
    if ( noChannel = FALSE ) {
        L7:recv_event(evtRecv, self, currentState[self]); 
    } else {
        evtRecv := idx_event_NullEvent;
    };


    \* transitions idx_state_BothOff[ 
    L8:
    either {

        \*     (F:'';L:32;C:1) BothOff --> WallOff LampSwitch[]/ (t32)
        await (evtRecv = idx_event_LampSwitch);
        visitedTransitions["t32"] := TRUE;

        newState := idx_state_WallOff; 
        goto entry_WallOff;

    } or {

        \*     (F:'';L:35;C:1) BothOff --> LampOff WallSwitch[]/ (t35)
        await (evtRecv = idx_event_WallSwitch);
        visitedTransitions["t35"] := TRUE;

        newState := idx_state_LampOff; 
        goto entry_LampOff;

    }; \* either
    \*]transitions idx_state_BothOff

\*]state idx_state_BothOff


\* state idx_state_LampOff[

entry_LampOff: skip;
    currentState[self] := newState;


body_LampOff: skip;
progress_LampOff: skip;
    if ( noChannel = FALSE ) {
        L9:recv_event(evtRecv, self, currentState[self]); 
    } else {
        evtRecv := idx_event_NullEvent;
    };


    \* transitions idx_state_LampOff[ 
    L10:
    either {

        \*     (F:'';L:36;C:1) LampOff --> BothOff WallSwitch[]/ (t36)
        await (evtRecv = idx_event_WallSwitch);
        visitedTransitions["t36"] := TRUE;

        newState := idx_state_BothOff; 
        goto entry_BothOff;

    } or {

        \*     (F:'';L:43;C:1) LampOff --> On LampSwitch[]/ (t43)
        await (evtRecv = idx_event_LampSwitch);
        visitedTransitions["t43"] := TRUE;

        newState := idx_state_On; 
        goto entry_On;

    }; \* either
    \*]transitions idx_state_LampOff

\*]state idx_state_LampOff


\* state idx_state_On[

entry_On: skip;
    currentState[self] := newState;


body_On: skip;
progress_On: skip;
    if ( noChannel = FALSE ) {
        L11:recv_event(evtRecv, self, currentState[self]); 
    } else {
        evtRecv := idx_event_NullEvent;
    };


    \* transitions idx_state_On[ 
    L12:
    either {

        \*     (F:'';L:40;C:1) On --> WallOff LampSwitch[]/ (t40)
        await (evtRecv = idx_event_LampSwitch);
        visitedTransitions["t40"] := TRUE;

        newState := idx_state_WallOff; 
        goto entry_WallOff;

    } or {

        \*     (F:'';L:46;C:1) On --> LampOff WallSwitch[]/ (t46)
        await (evtRecv = idx_event_WallSwitch);
        visitedTransitions["t46"] := TRUE;

        newState := idx_state_LampOff; 
        goto entry_LampOff;

    }; \* either
    \*]transitions idx_state_On

\*]state idx_state_On


\* state idx_state_WallOff[

entry_WallOff: skip;
    currentState[self] := newState;


body_WallOff: skip;
progress_WallOff: skip;
    if ( noChannel = FALSE ) {
        L13:recv_event(evtRecv, self, currentState[self]); 
    } else {
        evtRecv := idx_event_NullEvent;
    };


    \* transitions idx_state_WallOff[ 
    L14:
    either {

        \*     (F:'';L:33;C:1) WallOff --> BothOff LampSwitch[]/ (t33)
        await (evtRecv = idx_event_LampSwitch);
        visitedTransitions["t33"] := TRUE;

        newState := idx_state_BothOff; 
        goto entry_BothOff;

    } or {

        \*     (F:'';L:39;C:1) WallOff --> On WallSwitch[]/ (t39)
        await (evtRecv = idx_event_WallSwitch);
        visitedTransitions["t39"] := TRUE;

        newState := idx_state_On; 
        goto entry_On;

    }; \* either
    \*]transitions idx_state_WallOff

\*]state idx_state_WallOff

} \* region_r30 Switch


} \* algorithm switch

**********************************************************************)



=======================================================================
