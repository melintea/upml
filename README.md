# upml - from plantuml to promela

A tool to convert an UML state machine (a subset of the whole spec) to:
- a [promela model](README.spin.md) for [spin](https://github.com/nimble-code/Spin) checking. 
- a [TLA model](README.tla.md)

The state machine is described in an plantuml file (again, a subset of what plantuml offers).

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

## Similar tools

- ```vUML```. I could not get my hands on it.
- [Translating UML State Machine Diagram into Promela](https://www.iaeng.org/publication/IMECS2017/IMECS2017_pp512-516.pdf)
- TLA+
  - [Lamport](https://lamport.azurewebsites.net/tla/standalone-tools.html?back-link=tools.html)
  - [presenation & links](https://www.moritz.systems/blog/an-introduction-to-formal-verification/)

