# upml - from plantuml to promela

A tool to convert a plantuml state machine to promela for [spin](https://github.com/nimble-code/Spin) checking.

WIP, nothing to see yet.

## Status

@see [the plantuml state diagram](https://plantuml.com/state-diagram):

- unsupported: ```state "long state name" as xxx``` declarations 
- unsupported: history
- unsupported: fork, join
- idem: choice
- idem: entry/exit point
- idem: pin
- idem: expansion
- idem: json

Additions:
- comments: //, /**/
- transition: state --> state : event [guard]/effect

## Build

Depends on boost (spirit, program_options).

## Usage

Notes:
- each region executes in its own thread.
- a state execute in thread's region that owns it unless it has 
  multiple regions regions, in which case all its regions 
  are threaded separately from the owning region.

```
./upml --in ../plantuml/t0.plantuml --out ./t0.promela -- dump ./to.upml

# or
cat ../plantuml/t0.plantuml | ./umpl > ./t0.promela

TBD
```

