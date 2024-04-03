# upml - from plantuml to promela

A tool to convert a plantuml state machine to promela for [spin](https://github.com/nimble-code/Spin) checking.

WIP, nothing to see yet.

## Status

@see [the plantuml state diagram](https://plantuml.com/state-diagram):

- unsupported: history
- unsupported: fork, join
- idem: state alias
- idem: choice
- idem: entry/exit point
- idem: pin
- idem: expansion
- idem: inline color
- idem: skinparam
- idem: style
- idem: json

Additions:
- comments: #, //, /**/
- transition: state --> state : event [guard]/effect

## Usage

TBD

