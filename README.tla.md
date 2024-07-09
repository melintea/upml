- [Install](#install)
- [Status](#status)
- [Usage](#usage)
  - [Cheat sheet](#cheat-sheet)
  - [A lamp switch](#a-lamp-switch)
  - [SIP stuff](#sip-stuff)
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

Use the Promela model.

As of now:
- can translate model to pluscal which can translate to TLA+
- the generated model is not useable
  - closing the system: needs a way to stop infinite runs
  - closing the system: needs a way to coordinate between processes
  - but more important: the checks do not detect a transition that is never taken (and this could be a genuine logic error of the UML machine we are trying to model)

## Usage

### Cheat sheet

Command line (or use the tla-bin wrapper scripts above):
```
java -cp tla2tools.jar tla2sany.SANY -help  # The TLA⁺ parser
java -cp tla2tools.jar tlc2.TLC -help       # The TLA⁺ finite model checker
java -cp tla2tools.jar tlc2.REPL            # Enter the TLA⁺ REPL
java -cp tla2tools.jar pcal.trans -help     # The PlusCal-to-TLA⁺ translator
java -cp tla2tools.jar tla2tex.TLA -help    # The TLA⁺-to-LaTeX translator
```

Configuration file settings (to the best of my knowledge):
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

### A lamp switch

```
./upml --in ../plantuml/switch/switch.plantuml --out ../plantuml/switch/switch.tla --backend tla
```

### SIP stuff

```
./upml --in ../plantuml/sip/sip.plantuml --out ../plantuml/sip/sip.tla --backend tla
```

## Varia

- [Lamport](https://lamport.azurewebsites.net/tla/standalone-tools.html?back-link=tools.html)
- [All kinds of resources](https://learntla.com/reference/other-resources.html)
- [presentation & links](https://www.moritz.systems/blog/an-introduction-to-formal-verification/)

