## Syntax

**Notes**

* **Case-sensitive!**
* Self-transitions ([exit state & enter it again](uml.md)) are not supported and are implemented as internal transitions.
* Resulting HSM/FSM models respect run-to-completion (RTC) semantics.
* Canonical execution order (CEO):

  * is respected by FSM.
  * is not respected by HSM; HSM execution order is: transition actions then state exit actions then state enter actions.

**Plantuml** limitations: @see [the plantuml state diagram](https://plantuml.com/state-diagram):

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

**Additions**:

- comments: ```//```, non-nested ```/**/```. Plantuml will choke on these: if you can, use ```note``` instead.
- ```ltl```: these are model artifacts but due to plantuml quirks, the LTL formulas have to be scoped anywhere in a top level state. See the [SIP](sip.md) page example:
  - ```ClosedSystemEnvironment: ltl: ltlFinalStates {[]<>(state:ClosedSystemEnvironment:currentState == state:CallEnded && (state:Alice:currentState == state:Aterminated && (state:Bob:currentState == state:Bterminated)};```
- variable declarations: ```type name = value;```
  - at state level: ```state: localvar: bool lightOn = false;```;
  - at global level: ```AnyState: globalvar: bool lightOn = false;```;
- transition: ```state --> state : event [guard]/effect ;```
  - note the ending ```;```
  - currently the effect can be:
    - a ```send``` statement: ```send event:INVITE to state:Bob ;```
    - a ```trace``` statement: ```trace t1 foo bar baz ;```
    - a simple statement terminated by a ```;```. Examples:
      - ```send event:INVITE to state:Bob ;```
      - ```lightOn = true ;```
    - a (multi-)statement:
      - ```stmt one \; stmt two \; ;``` Note the escaped semicolons and the ending one
  - ```guard``` is an expression e.g. ```((x==y) && (z!=1 || z!=2))```
  - example: ```Deploy -1down-> Operation : BYE [((x==y) && (z!=1 || z!=2))] / send event:ACK to state:Bob ; ```
  - example: ``` Super1 --> Super2 : T1 [g()]/trace t1 foo bar baz;``` (note the lack of quotes)
- state actions: ```entry```, ```exit``` : same as transition effects
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
