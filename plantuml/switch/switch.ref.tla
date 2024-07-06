/*
Model for the double switch: https://learntla.com/topics/state-machines.html
*/

---- MODULE switch ----------------------------------------------------

EXTENDS TLC, Integers, Sequences

(* constants disguised as vars *)
idx_state_Unknown == -1
idx_state_Min == 0 
idx_state_BothOff == 0
idx_state_LampOff == 1
idx_state_WallOff == 2
idx_state_On == 3
idx_state_Max == 3

idx_event_Unknown == -1
idx_event_Min == 0 
idx_event_LampSwitch == 0
idx_event_WallSwitch == 1
idx_event_Max == 1
idx_event_SendRecvTest == 42

idx_proc_Unknown == -1
idx_proc_Min == 1  \* must be 1-based for the channels' tuple
idx_proc_Switch == 1
idx_proc_Env == 2
idx_proc_Max == 2

(**********************************************************************

--algorithm lamp {
variables   
    
    eventSink_Switch = << >>;
    \* channels = [i \in {idx_proc_Min..idx_proc_Max} |-> << >>];
    channels = << <<>>, <<>> >>;
    
    v1 \in {1..1000};
    v2 \in {1, 2, 3};

macro send_event(evt, from, to) {
    print <<"P:", from, "o->", evt, " > P:", to>>;
    channels[to] := Append(@, evt);
}
macro recv_event(evt, to) {
    await Len(channels[to]) > 0;
    evt := Head(channels[to]);
    print <<"P:", to, "<-i", evt>>;
    channels[to] := Tail(@);
}

fair+ process (Switch \in {idx_proc_Switch})
variables
    state \in {"BothOff", "WallOff", "LampOff", "On"};
    initialState = "BothOff";
    finalState  = "On";
    currentState  = idx_state_Unknown;
    evtRecv = idx_event_Unknown;
    myProcIdx = self;
{
  ProcBody:
    state := "BothOff";
    currentState := idx_state_Unknown;
    v1 := 2;
    v2 := 3;
    
    assert( Len(channels) = idx_proc_Max );
    print channels; \*error: print channels[myProcIdx]
    S:send_event(idx_event_SendRecvTest, self, self);
    print channels;
    R:recv_event(evtRecv, self);
    print channels;
    assert(evtRecv = idx_event_SendRecvTest);
    
  EntryBothOff:
    skip;
  BodyBothOff:
    either {
        await (/\ state = initialState /\ v1 = 3); \* <== dead !!
        print <<myProcIdx, ": moving to WallOff", v1>>;
        state := "WallOff";
        assert(TRUE);
        goto BodyWallOff;
    } or {
        await (/\ state = initialState);
        print <<myProcIdx, ": moving to LampOff", v1>>;
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

**********************************************************************)

\* BEGIN TRANSLATION (chksum(pcal) = "dce3ec9" /\ chksum(tla) = "2b033f9a")
\* Label ProcBody of process Switch at line 64 col 5 changed to ProcBody_
VARIABLES eventSink_Switch, channels, v1, v2, pc, state, initialState, 
          finalState, currentState, evtRecv, myProcIdx

vars == << eventSink_Switch, channels, v1, v2, pc, state, initialState, 
           finalState, currentState, evtRecv, myProcIdx >>

ProcSet == ({idx_proc_Switch}) \cup {200}

Init == (* Global variables *)
        /\ eventSink_Switch = << >>
        /\ channels = << <<>>, <<>> >>
        /\ v1 \in {1..1000}
        /\ v2 \in {1, 2, 3}
        (* Process Switch *)
        /\ state \in [{idx_proc_Switch} -> {"BothOff", "WallOff", "LampOff", "On"}]
        /\ initialState = [self \in {idx_proc_Switch} |-> "BothOff"]
        /\ finalState = [self \in {idx_proc_Switch} |-> "On"]
        /\ currentState = [self \in {idx_proc_Switch} |-> idx_state_Unknown]
        /\ evtRecv = [self \in {idx_proc_Switch} |-> idx_event_Unknown]
        /\ myProcIdx = [self \in {idx_proc_Switch} |-> self]
        /\ pc = [self \in ProcSet |-> CASE self \in {idx_proc_Switch} -> "ProcBody_"
                                        [] self = 200 -> "ProcBody"]

ProcBody_(self) == /\ pc[self] = "ProcBody_"
                   /\ state' = [state EXCEPT ![self] = "BothOff"]
                   /\ currentState' = [currentState EXCEPT ![self] = idx_state_Unknown]
                   /\ v1' = 2
                   /\ v2' = 3
                   /\ Assert(( Len(channels) = idx_proc_Max ), 
                             "Failure of assertion at line 69, column 5.")
                   /\ PrintT(channels)
                   /\ pc' = [pc EXCEPT ![self] = "S"]
                   /\ UNCHANGED << eventSink_Switch, channels, initialState, 
                                   finalState, evtRecv, myProcIdx >>

S(self) == /\ pc[self] = "S"
           /\ PrintT(<<"P:", self, "o->", idx_event_SendRecvTest, " > P:", self>>)
           /\ channels' = [channels EXCEPT ![self] = Append(@, idx_event_SendRecvTest)]
           /\ PrintT(channels')
           /\ pc' = [pc EXCEPT ![self] = "R"]
           /\ UNCHANGED << eventSink_Switch, v1, v2, state, initialState, 
                           finalState, currentState, evtRecv, myProcIdx >>

R(self) == /\ pc[self] = "R"
           /\ Len(channels[self]) > 0
           /\ evtRecv' = [evtRecv EXCEPT ![self] = Head(channels[self])]
           /\ PrintT(<<"P:", self, "<-i", evtRecv'[self]>>)
           /\ channels' = [channels EXCEPT ![self] = Tail(@)]
           /\ PrintT(channels')
           /\ Assert((evtRecv'[self] = idx_event_SendRecvTest), 
                     "Failure of assertion at line 75, column 5.")
           /\ pc' = [pc EXCEPT ![self] = "EntryBothOff"]
           /\ UNCHANGED << eventSink_Switch, v1, v2, state, initialState, 
                           finalState, currentState, myProcIdx >>

EntryBothOff(self) == /\ pc[self] = "EntryBothOff"
                      /\ TRUE
                      /\ pc' = [pc EXCEPT ![self] = "BodyBothOff"]
                      /\ UNCHANGED << eventSink_Switch, channels, v1, v2, 
                                      state, initialState, finalState, 
                                      currentState, evtRecv, myProcIdx >>

BodyBothOff(self) == /\ pc[self] = "BodyBothOff"
                     /\ \/ /\ (/\ state[self] = initialState[self] /\ v1 = 3)
                           /\ PrintT(<<myProcIdx[self], ": moving to WallOff", v1>>)
                           /\ state' = [state EXCEPT ![self] = "WallOff"]
                           /\ Assert((TRUE), 
                                     "Failure of assertion at line 84, column 9.")
                           /\ pc' = [pc EXCEPT ![self] = "BodyWallOff"]
                        \/ /\ (/\ state[self] = initialState[self])
                           /\ PrintT(<<myProcIdx[self], ": moving to LampOff", v1>>)
                           /\ state' = [state EXCEPT ![self] = "LampOff"]
                           /\ pc' = [pc EXCEPT ![self] = "BodyLampOff"]
                     /\ UNCHANGED << eventSink_Switch, channels, v1, v2, 
                                     initialState, finalState, currentState, 
                                     evtRecv, myProcIdx >>

BodyLampOff(self) == /\ pc[self] = "BodyLampOff"
                     /\ \/ /\ state[self] = "LampOff"
                           /\ state' = [state EXCEPT ![self] = "BothOff"]
                           /\ pc' = [pc EXCEPT ![self] = "BodyBothOff"]
                        \/ /\ state[self] = "LampOff"
                           /\ state' = [state EXCEPT ![self] = "On"]
                           /\ pc' = [pc EXCEPT ![self] = "BodyOn"]
                     /\ UNCHANGED << eventSink_Switch, channels, v1, v2, 
                                     initialState, finalState, currentState, 
                                     evtRecv, myProcIdx >>

BodyWallOff(self) == /\ pc[self] = "BodyWallOff"
                     /\ \/ /\ state[self] = "WallOff"
                           /\ state' = [state EXCEPT ![self] = "BothOff"]
                           /\ pc' = [pc EXCEPT ![self] = "BodyBothOff"]
                        \/ /\ state[self] = "WallOff"
                           /\ state' = [state EXCEPT ![self] = "On"]
                           /\ pc' = [pc EXCEPT ![self] = "BodyOn"]
                     /\ UNCHANGED << eventSink_Switch, channels, v1, v2, 
                                     initialState, finalState, currentState, 
                                     evtRecv, myProcIdx >>

BodyOn(self) == /\ pc[self] = "BodyOn"
                /\ \/ /\ state[self] = "On"
                      /\ state' = [state EXCEPT ![self] = "LampOff"]
                      /\ pc' = [pc EXCEPT ![self] = "BodyLampOff"]
                   \/ /\ state[self] = "On"
                      /\ state' = [state EXCEPT ![self] = "WallOff"]
                      /\ pc' = [pc EXCEPT ![self] = "BodyWallOff"]
                /\ UNCHANGED << eventSink_Switch, channels, v1, v2, 
                                initialState, finalState, currentState, 
                                evtRecv, myProcIdx >>

Switch(self) == ProcBody_(self) \/ S(self) \/ R(self) \/ EntryBothOff(self)
                   \/ BodyBothOff(self) \/ BodyLampOff(self)
                   \/ BodyWallOff(self) \/ BodyOn(self)

ProcBody == /\ pc[200] = "ProcBody"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![200] = "Done"]
            /\ UNCHANGED << eventSink_Switch, channels, v1, v2, state, 
                            initialState, finalState, currentState, evtRecv, 
                            myProcIdx >>

ClosedEnv == ProcBody

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == ClosedEnv
           \/ (\E self \in {idx_proc_Switch}: Switch(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {idx_proc_Switch} : SF_vars(Switch(self))
        /\ WF_vars(ClosedEnv)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
