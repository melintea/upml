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
INVARIANT
INVARIANTS
PROPERTY
PROPERTIES
CONSTANT
CONSTANTS
CONSTRAINT
CONSTRAINTS
ACTION_CONSTRAINT
ACTION_CONSTRAINTS
INIT
NEXT
VIEW
SYMMETRY
TYPE
TYPE_CONSTRAINT
```

## Varia

- [All kinds of resources](https://learntla.com/reference/other-resources.html)

