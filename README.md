# upml - formal verification of UML state machines with Promela and TLA+/PlusCal

A tool to convert (a subset of the whole [spec](https://www.omg.org/spec/UML/2.5.1/PDF) of) an UML state machine/statechart to:
- a [Promela model](README.spin.md) for [spin](https://github.com/nimble-code/Spin) checking. 
- a [TLA model](README.tla.md)

The state machine is described in an plantuml file (again, a subset of what plantuml offers) with some additions.

## Status

Finite state machines (FSM) should be fully supported. Hierarchical state machines (HSM) are only partially supported currently: only one hierachical level.

Self-transitions ([exit state & enter it again](doc/uml.md)) are not supported and are implemented as internal transitions.

Resulting models might violate run-to-completion (RTC) semantics. This might accurately reflect usage of the real state machine implementation in a multi-threaded environment.

Plantuml: @see [the plantuml state diagram](https://plantuml.com/state-diagram):

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
- ```ltl```: these are model artifacts but due to plantuml quirks, the LTL formulas have to be scoped anywhere in a top level state. See the [Promela](README.spin.md#sip-stuff) page example:
  - ```ClosedSystemEnvironment: ltl: ltlFinalStates {[]<>(state:ClosedSystemEnvironment:currentState == state:CallEnded && (state:Alice:currentState == state:Aterminated && (state:Bob:currentState == state:Bterminated)};```
- transition: ```state --> state : event [guard]/effect ;```
  - note the ending ```;```
  - currently the effect can only be a ```send``` or a ```trace``` action.
  - ```guard``` is an expression e.g. ```((x==y) && (z!=1 || z!=2))```
  - example: ```Deploy -1down-> Operation : BYE [((x==y) && (z!=1 || z!=2))] / send event:ACK to state:Bob ; ```
  - example: ```  Super1 --> Super2 : T1 [g()]/trace t1 foo bar baz; ``` (note the lack of quotes)
- state actions: ```entry```, ```exit```
  - ```send``` event from state:
  - example: ```AInitiated: entry: send event:INVITE to state:Bob ;```
- preconditions: ```state: precondition: expression ; ```
    - example: ```BInitiated: precondition: (state:BobcurrentState != state:AIdle);```
- postconditions: ```state: postcondition: expression ;```
- invariants: ```state: invariant: expression ;```
- configuration:
  - ```config: noInboundEvents```: this state receives no events
  - ```config: progressTag```: mark state as normal in an infinite execution cycle for starvation/non-progress loops verifications
- ```NullEvent```: reserved event name to force transitions statements to be executable without an external event
- timeout: ```WIP``` (not to be confused with the Promela ```timeout``` condition)

## Build

Depends on boost (spirit, program_options, filesystem). Requires C++20 or later.

## Similar tools & various links

- ```vUML```. I could not get my hands on it.
- [An exhausting list of FSL](https://buttondown.email/hillelwayne/archive/formal-specification-languages/)
- [SysML](https://sysml.org/)
- [qhsmtst/qtools](https://www.state-machine.com/qtools/qutest_qhsm.html)

