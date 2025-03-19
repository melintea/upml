- [Install](#install)
- [Status](#status)
- [Model](#model)
- [Differences with PlusCal](#differences-with-pluscal)
- [Usage](#usage)
- [Cheat sheet](#cheat-sheet)
- [Varia](#varia)

## Install

- [with snap](https://snapcraft.io/tlaplus)
- from [github](https://github.com/tlaplus/tlaplus/releases)
  - fetch the gtk zip and maybe the latest tla2tools.jar
  - unzip in a folder
  - replace the jar if newer
  - run toolbox/toolbox
- install [tlapm](https://github.com/tlaplus/tlapm)
- fetch the command line [wrappers](https://github.com/pmer/tla-bin)

Alternative toolbox: [Apalache](https://apalache.informal.systems/)

## Status

A couple of hacks:

- The basic toolbox checks do not detect a transition that is never taken (and this could be a genuine logic error of the UML machine we are trying to model). I had to add an ```AllTransitionsVisited``` temporal property. This unreacheable code check comes for free with Promela and now I wonder what other checks have to be coded...
- I had to add an ```MaxEventsReached``` temporal property to limit infinite runs. This also comes (almost) for free with Promela. 
Adjust ```maxUmlEvents``` as needed and note it is a negative. I could have used a CONSTANT here but - ideally - all the artifacts are contained in the model file.

## Model

- There is at least one region in the state machine.
- Each region executes in its own (promela) process.
- A composite state executes in its own region - it has at
  least one region.
- A simple state executes in the composite state/region 
  that owns it. 
- Events are asynchronous messages. Event names are unique per 
  plantuml file.
- State names are unique per plantuml file.

## Differences with PlusCal

See the [Promela](spin.md#differences-with-pluscal) page.

## Usage

Add ```MaxEventsReached```, ```AllTransitionsVisited```, ```UmlInvariants``` to the model: ![image](images/tla1.png).

These would be under ```PROPERTY``` in the config file for the model.

## Cheat sheet

Command line (or use the tla-bin wrapper scripts above):
```
java -cp tla2tools.jar tla2sany.SANY -help  # The TLA parser
java -cp tla2tools.jar tlc2.TLC -help       # The TLA finite model checker
java -cp tla2tools.jar tlc2.REPL            # Enter the TLA REPL
java -cp tla2tools.jar pcal.trans -help     # The PlusCal-to-TLA translator
java -cp tla2tools.jar tla2tex.TLA -help    # The TLA-to-LaTeX translator
```

Configuration file settings (to the best of my current knowledge):
```
ACTION_CONSTRAINT
ACTION_CONSTRAINTS
CONSTANT
CONSTANTS
CONSTRAINT
CONSTRAINTS
INIT
INVARIANT
INVARIANTS
PROPERTY
PROPERTIES
NEXT
SYMMETRY
TYPE
TYPE_CONSTRAINT
VIEW
```

## Varia

- [Lamport](https://lamport.azurewebsites.net/tla/standalone-tools.html?back-link=tools.html)
- [All kinds of resources](https://learntla.com/reference/other-resources.html)
- [Presentation & links](https://www.moritz.systems/blog/an-introduction-to-formal-verification/)

