## Install spin

```
sudo apt install spin
```
Note: this lacks xspin and other tools included in the distribution.

[comment]<details>
[comment]<summary>From source</summary>
From source:

```
git clone https://github.com/nimble-code/Spin.git
cd Spin
make # result: Src/spin

#xspin is under optional_gui/ispin.tcl
```
[comment]</details>

## Usage

Notes:
- there is at least one region in the state machine.
- each region executes in its own (promela) process.
- a composite state executes in its own region - it has at
  least one region.
- a simple state executes in the composite state/region 
  that owns it. 
- events are asynchronous messages. Event names are unique per 
  plantuml file.
- reserved:
  - state ```StateMachineEventGenerator```. It watches for state changes and injects "external" events as needed.
  - event ```StateChange```

### Cheat Sheet

(just use xspin/ispin.tcl)

```
# safety: assertions, non-reacheable code, race conditions
spin -a pmlfile
gcc -DSAFETY -o pan pan.c
./pan

# acceptance cycles
gcc -o pan pan.c
./pan -a

# non-progress cycles

gcc -DNP -o pan pan.c
./pan -l

```


### Simulation

To process this non-RFC3261-conformant-and-simplified [sip0.plantuml](plantuml/sip/sip0.plantuml):
![image](plantuml/sip/sip0.png)

```
./upml --in ../plantuml/sip/sip0.plantuml --out ./sip0.promela 

# or
cat ../plantuml/sip/sip0.plantuml | ./umpl > ./sip0.promela

# see e.g. https://spinroot.com/spin/Man/Manual.html
spin -c ./sip0.promela

# or
spin -a ./sip.promela
gcc -o pan pan.c
./pan -c0
...

```
And nothing happens:
```
spin -c sip.promela
proc 0 = :init:
proc 1 = region_r11
proc 2 = region_r20
proc 3 = region_r36
proc 4 = region_r37
      timeout      <<<========
-------------
final state:
-------------
#processes: 5
                queue 1 (_channels[0]):
                queue 2 (_channels[1]):
                queue 3 (_channels[2]):
                queue 4 (_channels[3]):
  4:    proc  4 (region_r37:1) sip.promela:278 (state 1)
  4:    proc  3 (region_r36:1) sip.promela:247 (state 1) <valid end state>
  4:    proc  2 (region_r20:1) sip.promela:157 (state 1)
  4:    proc  1 (region_r11:1) sip.promela:122 (state 1) <valid end state>
  4:    proc  0 (:init::1) sip.promela:360 (state 6) <valid end state>
5 processes created
```
It times out because nothing moves - it needs "external" events to be injected in the state machine. Note proc 2 is not in a valid state. One scenario would be for Alice to dial Bob which picks up then Alice hangs up. Add the StateMachineEventGenerator to run the state machine through this scenario [sip.plantuml](plantuml/sip/sip.plantuml):

```
[*] --> StateMachineEventGenerator 
StateMachineEventGenerator: entry: send event:Dial to state:Alice;
StateMachineEventGenerator --> StateMachineEventGenerator : StateChange [evtRecv.fromState == state:BInitiated] /send event:Pickup to state:Bob;
StateMachineEventGenerator --> StateMachineEventGenerator : StateChange [evtRecv.fromState == state:AEstablished] /send event:Hangup to state:Alice;
--
```

Now we get some results:
```
# Complete call scenario
spin -c sip.promela
...
      timeout
-------------
final state:
-------------
#processes: 5
                queue 1 (_channels[0]):
                queue 2 (_channels[1]):
                queue 3 (_channels[2]):
                queue 4 (_channels[3]):
                queue 5 (_channels[4]):
357:    proc  4 (region_r36:1) sip.promela:309 (state 1) <valid end state>
357:    proc  3 (region_r20:1) sip.promela:294 (state 67) <valid end state>
357:    proc  2 (region_r19:1) sip.promela:188 (state 1) <valid end state>
357:    proc  1 (region_r11:1) sip.promela:132 (state 7) <valid end state>
357:    proc  0 (:init::1) sip.promela:423 (state 7) <valid end state>

```

Same timeout diagnostic but all processes are in a valid end state now. Had Bob not picked up the call, we would end up again in a timeout with an invalid state. So one flaw of the machine is it is missing the Tx timers: 
```
# Bob does not pick up
spin -c sip.promela
...
      timeout
-------------
final state:
-------------
#processes: 6
                queue 1 (_channels[0]):
                queue 2 (_channels[1]):
                queue 3 (_channels[2]):
                queue 4 (_channels[3]):
                queue 5 (_channels[4]):
131:    proc  5 (region_r37:1) sip.promela:336 (state 1)
131:    proc  4 (region_r36:1) sip.promela:305 (state 1) <valid end state>
131:    proc  3 (region_r20:1) sip.promela:215 (state 1)
131:    proc  2 (region_r19:1) sip.promela:184 (state 1) <valid end state>
131:    proc  1 (region_r11:1) sip.promela:131 (state 7) <valid end state>
131:    proc  0 (:init::1) sip.promela:419 (state 7) <valid end state>
6 processes created

```


### Verification

WIP

