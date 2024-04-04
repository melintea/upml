# upml - from plantuml to promela

A tool to convert a plantuml state machine to promela for [spin](https://github.com/nimble-code/Spin) checking.

WIP, nothing to see yet.

## Status

@see [the plantuml state diagram](https://plantuml.com/state-diagram):

- unsupported: declarations of state long names
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

Depends on boost (spirit, optional).

## Usage

TBD

