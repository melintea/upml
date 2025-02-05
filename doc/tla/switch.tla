/*
Experimentation ground.
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
idx_event_Max == 42
idx_event_SendRecvTest == 42

idx_proc_Unknown == -1
idx_proc_Min == 1  \* must be 1-based for the channels' tuple
idx_proc_Switch == 1
idx_proc_Env == 2
idx_proc_Max == 2

(**********************************************************************

--algorithm lamp {
variables   
    
    \* channels = [i \in {idx_proc_Min..idx_proc_Max} |-> << >>];
    channels = << <<>>, <<>> >>;
    
    v1 \in {1..1000};
    v2 \in {1, 2, 3};

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

fair+ process (Switch \in {idx_proc_Switch})
variables
    state \in {"BothOff", "WallOff", "LampOff", "On"};
    initialState = "BothOff";
    finalState  = "On";
    currentState  = idx_state_Unknown;
    evtRecv = idx_event_Unknown;
    myProcIdx = self;
    hasChannel = TRUE;
{
  ProcBody:
    state := "BothOff";
    currentState := idx_state_Unknown;
    v1 := 2;
    v2 := 3;
    
    assert( Len(channels) = idx_proc_Max );
    if (hasChannel) {
      print channels; \*error: print channels[myProcIdx]
      S:send_event(idx_event_SendRecvTest, self, self);
      print channels;
      R:recv_event(evtRecv, self);
      print channels;
      assert(evtRecv = idx_event_SendRecvTest);
    };
    
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

\* BEGIN TRANSLATION (chksum(pcal) = "89f8bf47" /\ chksum(tla) = "8f5feac3")
\* Label ProcBody of process Switch at line 69 col 5 changed to ProcBody_
VARIABLES channels, v1, v2, pc, state, initialState, finalState, currentState, 
          evtRecv, myProcIdx, hasChannel

vars == << channels, v1, v2, pc, state, initialState, finalState, 
           currentState, evtRecv, myProcIdx, hasChannel >>

ProcSet == ({idx_proc_Switch}) \cup {200}

Init == (* Global variables *)
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
        /\ hasChannel = [self \in {idx_proc_Switch} |-> TRUE]
        /\ pc = [self \in ProcSet |-> CASE self \in {idx_proc_Switch} -> "ProcBody_"
                                        [] self = 200 -> "ProcBody"]

ProcBody_(self) == /\ pc[self] = "ProcBody_"
                   /\ state' = [state EXCEPT ![self] = "BothOff"]
                   /\ currentState' = [currentState EXCEPT ![self] = idx_state_Unknown]
                   /\ v1' = 2
                   /\ v2' = 3
                   /\ Assert(( Len(channels) = idx_proc_Max ), 
                             "Failure of assertion at line 74, column 5.")
                   /\ IF hasChannel[self]
                         THEN /\ PrintT(channels)
                              /\ pc' = [pc EXCEPT ![self] = "S"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "EntryBothOff"]
                   /\ UNCHANGED << channels, initialState, finalState, evtRecv, 
                                   myProcIdx, hasChannel >>

S(self) == /\ pc[self] = "S"
           /\ PrintT(<<"P:", self, "o->", idx_event_SendRecvTest, " > P:", self>>)
           /\ Assert((self >= idx_proc_Min /\ self <= idx_proc_Max), 
                     "Failure of assertion at line 44, column 5 of macro called at line 77, column 9.")
           /\ Assert((self >= idx_proc_Min /\ self <= idx_proc_Max), 
                     "Failure of assertion at line 45, column 5 of macro called at line 77, column 9.")
           /\ Assert((idx_event_SendRecvTest >= idx_event_Min /\ idx_event_SendRecvTest <= idx_event_Max), 
                     "Failure of assertion at line 46, column 5 of macro called at line 77, column 9.")
           /\ channels' = [channels EXCEPT ![self] = Append(@, idx_event_SendRecvTest)]
           /\ PrintT(channels')
           /\ pc' = [pc EXCEPT ![self] = "R"]
           /\ UNCHANGED << v1, v2, state, initialState, finalState, 
                           currentState, evtRecv, myProcIdx, hasChannel >>

R(self) == /\ pc[self] = "R"
           /\ Assert((self >= idx_proc_Min /\ self <= idx_proc_Max), 
                     "Failure of assertion at line 50, column 5 of macro called at line 79, column 9.")
           /\ Len(channels[self]) > 0
           /\ evtRecv' = [evtRecv EXCEPT ![self] = Head(channels[self])]
           /\ PrintT(<<"P:", self, "<-i", evtRecv'[self]>>)
           /\ Assert((evtRecv'[self] >= idx_event_Min /\ evtRecv'[self] <= idx_event_Max), 
                     "Failure of assertion at line 54, column 5 of macro called at line 79, column 9.")
           /\ channels' = [channels EXCEPT ![self] = Tail(@)]
           /\ PrintT(channels')
           /\ Assert((evtRecv'[self] = idx_event_SendRecvTest), 
                     "Failure of assertion at line 81, column 7.")
           /\ pc' = [pc EXCEPT ![self] = "EntryBothOff"]
           /\ UNCHANGED << v1, v2, state, initialState, finalState, 
                           currentState, myProcIdx, hasChannel >>

EntryBothOff(self) == /\ pc[self] = "EntryBothOff"
                      /\ TRUE
                      /\ pc' = [pc EXCEPT ![self] = "BodyBothOff"]
                      /\ UNCHANGED << channels, v1, v2, state, initialState, 
                                      finalState, currentState, evtRecv, 
                                      myProcIdx, hasChannel >>

BodyBothOff(self) == /\ pc[self] = "BodyBothOff"
                     /\ \/ /\ (/\ state[self] = initialState[self] /\ v1 = 3)
                           /\ PrintT(<<myProcIdx[self], ": moving to WallOff", v1>>)
                           /\ state' = [state EXCEPT ![self] = "WallOff"]
                           /\ Assert((TRUE), 
                                     "Failure of assertion at line 91, column 9.")
                           /\ pc' = [pc EXCEPT ![self] = "BodyWallOff"]
                        \/ /\ (/\ state[self] = initialState[self])
                           /\ PrintT(<<myProcIdx[self], ": moving to LampOff", v1>>)
                           /\ state' = [state EXCEPT ![self] = "LampOff"]
                           /\ pc' = [pc EXCEPT ![self] = "BodyLampOff"]
                     /\ UNCHANGED << channels, v1, v2, initialState, 
                                     finalState, currentState, evtRecv, 
                                     myProcIdx, hasChannel >>

BodyLampOff(self) == /\ pc[self] = "BodyLampOff"
                     /\ \/ /\ state[self] = "LampOff"
                           /\ state' = [state EXCEPT ![self] = "BothOff"]
                           /\ pc' = [pc EXCEPT ![self] = "BodyBothOff"]
                        \/ /\ state[self] = "LampOff"
                           /\ state' = [state EXCEPT ![self] = "On"]
                           /\ pc' = [pc EXCEPT ![self] = "BodyOn"]
                     /\ UNCHANGED << channels, v1, v2, initialState, 
                                     finalState, currentState, evtRecv, 
                                     myProcIdx, hasChannel >>

BodyWallOff(self) == /\ pc[self] = "BodyWallOff"
                     /\ \/ /\ state[self] = "WallOff"
                           /\ state' = [state EXCEPT ![self] = "BothOff"]
                           /\ pc' = [pc EXCEPT ![self] = "BodyBothOff"]
                        \/ /\ state[self] = "WallOff"
                           /\ state' = [state EXCEPT ![self] = "On"]
                           /\ pc' = [pc EXCEPT ![self] = "BodyOn"]
                     /\ UNCHANGED << channels, v1, v2, initialState, 
                                     finalState, currentState, evtRecv, 
                                     myProcIdx, hasChannel >>

BodyOn(self) == /\ pc[self] = "BodyOn"
                /\ \/ /\ state[self] = "On"
                      /\ state' = [state EXCEPT ![self] = "LampOff"]
                      /\ pc' = [pc EXCEPT ![self] = "BodyLampOff"]
                   \/ /\ state[self] = "On"
                      /\ state' = [state EXCEPT ![self] = "WallOff"]
                      /\ pc' = [pc EXCEPT ![self] = "BodyWallOff"]
                /\ UNCHANGED << channels, v1, v2, initialState, finalState, 
                                currentState, evtRecv, myProcIdx, hasChannel >>

Switch(self) == ProcBody_(self) \/ S(self) \/ R(self) \/ EntryBothOff(self)
                   \/ BodyBothOff(self) \/ BodyLampOff(self)
                   \/ BodyWallOff(self) \/ BodyOn(self)

ProcBody == /\ pc[200] = "ProcBody"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![200] = "Done"]
            /\ UNCHANGED << channels, v1, v2, state, initialState, finalState, 
                            currentState, evtRecv, myProcIdx, hasChannel >>

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
