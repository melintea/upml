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
- each region executes in its own (promela) process.
- a state execute in the process/region that owns it unless it
  has multiple regions, in which case all its regions 
  are separate processes from the owning region.
- events are asynchronous messages. Event names are unique per 
  plantuml file.

To process [sip.plantuml]({{ site.baseurl }}/plantuml/sip.plantuml):
![image]({{ site.baseurl }}/plantuml/sip.png)

```
./upml --in ../plantuml/sip.plantuml --out ./sip.promela -- dump ./to.upml

# or
cat ../plantuml/sip.plantuml | ./umpl > ./sip.promela

# see e.g. https://spinroot.com/spin/Man/Manual.html
spin -c ./sip.promela

# or
spin -a ./sip.promela
gcc -o pan pan.c
./pan -c0
...

```

