# upml - from plantuml to promela

A tool to convert an UML state machine (a subset of the whole spec) to promela for [spin](https://github.com/nimble-code/Spin) checking. The state machine is described in an plantuml file (again, a subset of what plantuml offers).

## Status

@see [the plantuml state diagram](https://plantuml.com/state-diagram):

- unsupported: history
- unsupported: fork, join
- idem: choice
- idem: entry/exit point
- idem: pin
- idem: expansion
- unsupported plantuml constructs:
  - state declarations such as:
    - ```state "long state name" as xxx``` 
    - ```state ignoredAgain as "long name"```
  - json
  - skinparam

Additions:
- comments: ```//```, non-nested ```/**/```. Plantuml will choke on these: if you can, use ```note``` instead.
- transition: ```state --> state : event [guard]/effect ;```
  - currently the effect can only be a ```send``` action.
- state actions: ```entry```, ```exit```
  - ```send``` event from state:
    ```entry: send event:INVITE to state:Bob ;```
- TODO:
  - preconditions
  - postconditions
  - invariants
  - timeout

## Build

Depends on boost (spirit, program_options).

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

## Similar tools

- ```vUML```. I could not get my hands on it.
- [Translating UML State Machine Diagram into Promela](https://www.iaeng.org/publication/IMECS2017/IMECS2017_pp512-516.pdf)
- TLA+
  - [Lamport](https://lamport.azurewebsites.net/tla/standalone-tools.html?back-link=tools.html)
  - [presenation & links](https://www.moritz.systems/blog/an-introduction-to-formal-verification/)

