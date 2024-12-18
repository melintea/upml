- [Install spin](#install-spin)
- [Timeline editor](#timeline-editor)
- [Differences with PlusCal](#differences-with-pluscal)
- [Model](#model)
- [Cheat Sheet](#cheat-sheet)
- [A lamp switch](#a-lamp-switch)
  - [Simulation](#simulation)
  - [Verification](#verification)
- [SIP stuff](#sip-stuff)
  - [Simulation](#simulation-1)
  - [Verification](#verification-1)
- [Various links](#various-links)


## Install spin

```
sudo apt install spin
```
Note: this lacks xspin and other tools included in the distribution.

From source:

```
git clone https://github.com/nimble-code/Spin.git
cd Spin
make # result: Src/spin

#xspin is under optional_gui/ispin.tcl
```
Alternative GUI: jSpin:
- [code](https://github.com/motib/jspin). See also spinSpider.
- [install guide](https://gist.github.com/kocsenc/10130261)

## Timeline editor

Cannot find it. It was at http://cm.bell-labs.com/cm/cs/what/timeedit/index.html

## Differences with PlusCal

- atomicity: Promela is fine grained; atomicity is at statement level and coarser gained atomicity is achieved with 
  dedicated statement grouping: ```atomic```, ```d_step```. 
  PlusCal is coarse grained: atomicity is in between labels; much harder to diagnose race conditions in the model.
- dead model code: Promela will warn about code that was not reached during verification as this could be a model flaw. 
  PlusCal needs to be told which code is essential.
- process termination: a process that did not end or did not end in an ```end``` label at the end of the verification 
  will be flagged as an error with Promela.
  PlusCal has no support for end-in-the-middle diagnostic labels or such.
- process creation: PlusCal cannot dynamically create processes from within your model.
- you can verify multiple temporal formulas at once with TLC but only one at a time with spin; although you can
  consider aggregating multiple LTL formulas into one until it becomes impossible to read it.
- no ```timeout``` equivalent in TLA+ to get out of a deadlock.
- fairness: PlusCal has weak & strong fairness builtin. 
  Spin has only weak fairness builtin; strong fairness has to be [defined](https://spinroot.com/fluxbb/viewtopic.php?id=671) via LTL/never claims.

As an [comparative example](https://accu.org/journals/overload/32/183/melinte/), here is the Dekker algorithm implemented in:
- [Promela](https://spinroot.com/spin/Man/Manual.html)
- [PlusCal](https://github.com/duerrfk/skp/blob/master/criticalsection5dekker/criticalsection5dekker.tla)

## Model

- There is at least one region in the state machine.
- Each region executes in its own (promela) process.
- A composite state executes in its own region - it has at
  least one region.
- A simple state executes in the composite state/region 
  that owns it. 
- Events are asynchronous messages. Event names are unique per 
  plantuml file.
- State names are unique per plantuml file.

## Cheat Sheet

(just use [xspin/ispin.tcl](https://raw.githubusercontent.com/nimble-code/Spin/master/optional_gui/ispin.tcl) ). 

See also http://spinroot.com/spin/Man/4_SpinVerification.html

```
# simulation
# -i  interactive
spin pmlfile
```
```
#verification

# safety: assertions, non-reacheable code, race conditions, wrong end states, timout/deadlock + optional ltl
spin -a -f "![]ltl" > safety.ltl
spin -a -N safety.ltl pmlfile
gcc -DSAFETY -o pan pan.c
./pan

# acceptance (undesirable) cycles; -f / -DNFAIR: weak fairness
# "The accept label in this model formalizes the requirement that the second i
# state cannot persist forever, and cannot be revisited infinitely often either."
# -f optional weak fairness constraint
spin -a -f "!<>ltl" pmlfile
gcc -DNFAIR=numproc -o pan pan.c
./pan -a -f

# non-progress cycles/starvation
# -f optional weak fairness constraint
gcc -DNP -o pan pan.c
./pan -l -f
```
```
# error replay
# -p statements
# -g globals
# -l locals
# -s sent
# -r received
spin -t pmlfile
pan -t pmlfile
```
```
# reformat the model:
cat file | spin -pp | ...
```

```
@ slicing / model analysis
spin -A
```

## A lamp switch

A double (lamp & wall) switch lamp [switch.plantuml](plantuml/switch/switch.plantuml) model:
![image](plantuml/switch/switch0.png)

### Simulation

Left as above, only interactive simulation is possible, if ever. 
A "human" must be added to randomly flip the switches - the state machine needs 
the "environment" in which it operates for simulation and verification; verification 
needs a fully-specified/closed system.

Then wrap the switch spec into its own ```Switch``` composite state:

```
state Human {
  [*] --> Flip
  Flip: config: noInboundEvents;
  Flip --> Flip : NullEvent /send event:LampSwitch to state:Switch;
  Flip --> Flip : NullEvent /send event:WallSwitch to state:Switch;
}
```

![image](plantuml/switch/switch.png)


```
./upml --in ../plantuml/switch/switch.plantuml --out ../plantuml/switch/switch.promela --backend spin

# or
cat ../plantuml/switch/switch.plantuml | ./umpl > ../plantuml/switch/switch.promela

# see e.g. https://spinroot.com/spin/Man/Manual.html
spin -c -u200 ../plantuml/switch/switch.promela

# or
spin -a ./sip.promela
gcc -o pan pan.c
./pan -c0 -u200
...
```

```
spin -c -g -l -u200 ../plantuml/switch/switch.promela
proc 0 = :init:
proc 1 = region_r17
proc 2 = region_r19
proc 3 = region_r30
q\p   0   1   2   3
  3   .   .   _channels[2]!event_WallSwitch,1,5
  3   .   .   .   _channels[2]?event_WallSwitch,1,5
                  MSC: > 2 region_r30 event event_WallSwitch in state 0
  3   .   .   _channels[2]!event_WallSwitch,1,5
...

  3   .   .   .   _channels[2]?event_LampSwitch,1,5
                  MSC: > 2 region_r30 event event_LampSwitch in state 3
-------------
depth-limit (-u200 steps) reached
```

### Verification

Mark states as ```progressTag``` e.g. ```On: config: progressTag;``` for non-progress checks.
Use xspin/ispin.tcl.

## SIP stuff

A non-RFC3261-conformant-and-simplified [sip0.plantuml](plantuml/sip/sip0.plantuml) abominable SM:
![image](plantuml/sip/sip0.png)

### Simulation

Close the system with a "buggy" event generator. This generator can generate 
a) multiple events (e.g. Dial to Alice) as the spin machine moves through its 
intermediate states that do not change the SM states;
b) non-deterministically choose between multiple event possibilities as the 
spin machine moves through its intermediate states etc,etc:

```
state ClosedSystemEnvironment {
[*] --> EventGenerator 
EventGenerator: config: noInboundEvents;
EventGenerator --> EventGenerator : NullEvent [state:Alice:currentState == state:AIdle] /send event:Dial to state:Alice;
EventGenerator --> EventGenerator : NullEvent [state:Bob:currentState == state:BInitiated] /send event:Pickup to state:Bob;
EventGenerator --> EventGenerator : NullEvent [state:Alice:currentState == state:AEstablished] /send event:Hangup to state:Alice;
}
```
As a result, some simulations are good and some will timeout with the SM in some weird state.  Either
fix the issues exposed by spin in the abominable SM, either use a deterministic event generator with an LTL check:

```
state ClosedSystemEnvironment {
[*] --> AliceDial 
AliceDial: config: noInboundEvents;
AliceDial --> BobPickup : NullEvent [state:Alice:currentState == state:AIdle] /send event:Dial to state:Alice;

BobPickup: config: noInboundEvents;
BobPickup --> AliceHangup : NullEvent [state:Bob:currentState == state:BInitiated] /send event:Pickup to state:Bob;

AliceHangup: config: noInboundEvents;
AliceHangup --> CallEnded : NullEvent [state:Alice:currentState == state:AEstablished] /send event:Hangup to state:Alice;

CallEnded: config: noInboundEvents;
CallEnded --> [*]

ClosedSystemEnvironment: ltl: ltlFinalStates {<>[](state:ClosedSystemEnvironment:currentState == state:CallEnded && state:Alice:currentState == state:Aterminated && state:Bob:currentState == state:Bterminated)};
}
```
![image](plantuml/sip/sip.png)

A good run:

```
spin -c -g -l -u200 ../plantuml/sip/sip.promela
proc 0 = :init:
proc 1 = region_r13
proc 2 = region_r3
proc 3 = region_r35
proc 4 = region_r4
q\p   0   1   2   3   4
  1   .   .   .   .   _channels[0]!event_Dial,11,3
  1   .   _channels[0]?event_Dial,11,3
          MSC: > 0 region_r13 event event_Dial in state 1
  3   .   _channels[2]!event_INVITE,2,8
  3   .   .   .   _channels[2]?event_INVITE,2,8
                  MSC: > 2 region_r35 event event_INVITE in state 6
  3   .   .   .   .   _channels[2]!event_Pickup,11,8
  1   .   .   .   _channels[0]!event_1xx,7,3
  1   .   _channels[0]?event_1xx,7,3
          MSC: > 0 region_r13 event event_1xx in state 2
  3   .   .   .   _channels[2]?event_Pickup,11,8
                  MSC: > 2 region_r35 event event_Pickup in state 7
  3   .   .   .   .   _channels[2]!event_Pickup,11,8
  1   .   .   .   _channels[0]!event_2xx,5,3
  1   .   _channels[0]?event_2xx,5,3
          MSC: > 0 region_r13 event event_2xx in state 2
  3   .   .   .   _channels[2]?event_Pickup,11,8
                  MSC: > 2 region_r35 event event_Pickup in state 5
  1   .   .   .   .   _channels[0]!event_Hangup,11,3
  3   .   _channels[2]!event_ACK,0,8
  1   .   _channels[0]?event_Hangup,11,3
          MSC: > 0 region_r13 event event_Hangup in state 0
  1   .   .   .   .   _channels[0]!event_Hangup,11,3
  3   .   _channels[2]!event_BYE,4,8
  1   .   _channels[0]?event_Hangup,11,3
          MSC: > 0 region_r13 event event_Hangup in state 4
      timeout

```

### Verification

Use ```ltl```, ```precondition```, ```postcondition```, ```invariant```.

(The plantuml file contains a few useless precondition, postcondition & invariant statements for demo and testing)

Use xspin/ispin.tcl.

## Various links
- [Spin & Promela](https://spinroot.com)
- [Tau](https://data.caltech.edu/records/8exsc-7h074)
- [Total Store Ordering (TSO) and the Partial Store Ordering (PSO) memory models](https://github.com/plasklab/mmlib) & [usage](https://brilliantsugar.github.io/posts/how-i-learned-to-stop-worrying-and-love-juggling-c++-atomics/)
