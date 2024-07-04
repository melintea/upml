---- MODULE switch ----

(*--algorithm lamp
variable state = "BothOff";
process StateMachine = "SM"
begin
  Action:
    either \* this is the state machine
        await state = "BothOff";
        state := "WallOff";
      or
        await state = "BothOff";
        state := "LampOff";
    or
        await state = "LampOff";
        state := "BothOff";
      or
        await state = "LampOff";
        state := "On";
    or
        await state = "WallOff";
        state := "BothOff";
      or
        await state = "WallOff";
        state := "On";
    or
        await state = "On";
        state := "LampOff";
      or
        await state = "On";
        state := "WallOff";
    end either;
    goto Action;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "5c9b8d1e" /\ chksum(tla) = "b81ed61b")
VARIABLES state, pc

vars == << state, pc >>

ProcSet == {"SM"}

Init == (* Global variables *)
        /\ state = "BothOff"
        /\ pc = [self \in ProcSet |-> "Action"]

Action == /\ pc["SM"] = "Action"
          /\ \/ /\ state = "BothOff"
                /\ state' = "WallOff"
             \/ /\ state = "BothOff"
                /\ state' = "LampOff"
             \/ /\ state = "LampOff"
                /\ state' = "BothOff"
             \/ /\ state = "LampOff"
                /\ state' = "On"
             \/ /\ state = "WallOff"
                /\ state' = "BothOff"
             \/ /\ state = "WallOff"
                /\ state' = "On"
             \/ /\ state = "On"
                /\ state' = "LampOff"
             \/ /\ state = "On"
                /\ state' = "WallOff"
          /\ pc' = [pc EXCEPT !["SM"] = "Action"]

StateMachine == Action

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == StateMachine
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
