# upml - from plantuml to promela

A tool to convert a plantuml state machine to promela for [spin](https://github.com/nimble-code/Spin) checking.

WIP, nothing to see yet.

## Status

@see [the palntuml state diagram](https://plantuml.com/state-diagram):

- unsupported: state long name
- unsupported: history
- idem: fork, join
- idem: choice
- idem: entry/exit point
- idem: pin
- idem: expansion
- idem: note
- idem: inline color
- idem: skinparam
- idem: style
- idem: alias
- idem: json

Additions:
- comments: #, //, /**/
- transition: state --> state : event [guard]/effect

## Usage

TBD

