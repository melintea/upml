Model for the double switch: https://learntla.com/topics/state-machines.html

---- MODULE switch ----

EXTENDS TLC, Integers, Sequences

(**********************************************************************

--algorithm lamp {
variables   state \in {"BothOff", "WallOff", "LampOff", "On"}
          , v1 \in {1..1000}
          , v2 \in {1, 2, 3}
          ;

fair process (Switch = 100)
variables   initialState = "BothOff"
          , finalState  = "On"
          ;
{
  ProcBody:
    state := "BothOff";
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

\* BEGIN TRANSLATION (chksum(pcal) = "54f37938" /\ chksum(tla) = "c3ccec8a")
\* Label ProcBody of process Switch at line 21 col 5 changed to ProcBody_
VARIABLES state, v1, v2, pc, initialState, finalState

vars == << state, v1, v2, pc, initialState, finalState >>

ProcSet == {100} \cup {200}

Init == (* Global variables *)
        /\ state \in {"BothOff", "WallOff", "LampOff", "On"}
        /\ v1 \in {1..1000}
        /\ v2 \in {1, 2, 3}
        (* Process Switch *)
        /\ initialState = "BothOff"
        /\ finalState = "On"
        /\ pc = [self \in ProcSet |-> CASE self = 100 -> "ProcBody_"
                                        [] self = 200 -> "ProcBody"]

ProcBody_ == /\ pc[100] = "ProcBody_"
             /\ state' = "BothOff"
             /\ v1' = 2
             /\ v2' = 3
             /\ pc' = [pc EXCEPT ![100] = "EntryBothOff"]
             /\ UNCHANGED << initialState, finalState >>

EntryBothOff == /\ pc[100] = "EntryBothOff"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![100] = "BodyBothOff"]
                /\ UNCHANGED << state, v1, v2, initialState, finalState >>

BodyBothOff == /\ pc[100] = "BodyBothOff"
               /\ \/ /\ (/\ state = initialState /\ v1 = 3)
                     /\ PrintT(<<"Moving to WallOff", v1>>)
                     /\ state' = "WallOff"
                     /\ Assert((TRUE), 
                               "Failure of assertion at line 32, column 9.")
                     /\ pc' = [pc EXCEPT ![100] = "BodyWallOff"]
                  \/ /\ (/\ state = initialState)
                     /\ PrintT(<<"Moving to LampOff", v1>>)
                     /\ state' = "LampOff"
                     /\ pc' = [pc EXCEPT ![100] = "BodyLampOff"]
               /\ UNCHANGED << v1, v2, initialState, finalState >>

BodyLampOff == /\ pc[100] = "BodyLampOff"
               /\ \/ /\ state = "LampOff"
                     /\ state' = "BothOff"
                     /\ pc' = [pc EXCEPT ![100] = "BodyBothOff"]
                  \/ /\ state = "LampOff"
                     /\ state' = "On"
                     /\ pc' = [pc EXCEPT ![100] = "BodyOn"]
               /\ UNCHANGED << v1, v2, initialState, finalState >>

BodyWallOff == /\ pc[100] = "BodyWallOff"
               /\ \/ /\ state = "WallOff"
                     /\ state' = "BothOff"
                     /\ pc' = [pc EXCEPT ![100] = "BodyBothOff"]
                  \/ /\ state = "WallOff"
                     /\ state' = "On"
                     /\ pc' = [pc EXCEPT ![100] = "BodyOn"]
               /\ UNCHANGED << v1, v2, initialState, finalState >>

BodyOn == /\ pc[100] = "BodyOn"
          /\ \/ /\ state = "On"
                /\ state' = "LampOff"
                /\ pc' = [pc EXCEPT ![100] = "BodyLampOff"]
             \/ /\ state = "On"
                /\ state' = "WallOff"
                /\ pc' = [pc EXCEPT ![100] = "BodyWallOff"]
          /\ UNCHANGED << v1, v2, initialState, finalState >>

Switch == ProcBody_ \/ EntryBothOff \/ BodyBothOff \/ BodyLampOff
             \/ BodyWallOff \/ BodyOn

ProcBody == /\ pc[200] = "ProcBody"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![200] = "Done"]
            /\ UNCHANGED << state, v1, v2, initialState, finalState >>

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
