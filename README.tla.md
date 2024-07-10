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

Use the Promela model if you can. 

The basic toolbox checks do not detect a transition that is never taken (and this could be a genuine logic error of the UML machine we are trying to model). I guess the model needs to be completed with an appropriate check along the lines (WIP):
```
transitionLabels = { idx_t1, idx_t2,... };
visitedTransitions = [t \in transitionLabels |-> FALSE];
...set the flag on transition...
...
InvariantAllTransitionsTaken == <>(\A t in visitedTransitions : pc[t] = TRUE)

```

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

Close the system as described in the Promela page. Note: this will generate an infinite run (for now)

Then run upml and load the result in the toolbox.

```
./upml --in ../plantuml/switch/switch.plantuml --out ../plantuml/switch/switch.tla --backend tla
```

### SIP stuff

Close the system as described in the Promela page, run upml:

```
./upml --in ../plantuml/sip/sip.plantuml --out ../plantuml/sip/sip.tla --backend tla
```

Then use the toolbox with e.g. Temporal Formula: Spec and a Deadlock check:
```
...
End of statistics.
Progress(75) at 2024-07-10 11:48:04: 21,637 states generated (345,731 s/min), 6,568 distinct states found (104,948 ds/min), 0 states left on queue.
21637 states generated, 6568 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 75.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 4 and the 95th percentile is 2).
Finished in 3767ms at (2024-07-10 11:48:04)
```

## Varia

- [Lamport](https://lamport.azurewebsites.net/tla/standalone-tools.html?back-link=tools.html)
- [All kinds of resources](https://learntla.com/reference/other-resources.html)
- [presentation & links](https://www.moritz.systems/blog/an-introduction-to-formal-verification/)

