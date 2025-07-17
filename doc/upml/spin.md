- [Install spin](#install-spin)
- [Timeline editor](#timeline-editor)
- [Differences with PlusCal](#differences-with-pluscal)
- [Model](#model)
- [Cheat Sheet](#cheat-sheet)
- [LTL](#ltl)
- [Various links](#various-links)

## Install spin

```
sudo apt install spin
```
Note: this lacks xspin and other tools included in the distribution.

From source:

```
git clone https://github.com/nimble-code/Spin.git
cd Spin
make # result: Src/spin

#xspin is under optional_gui/ispin.tcl
```
Alternative GUI: 
- jSpin:
  - [code](https://github.com/motib/jspin). See also spinSpider.
  - [install guide](https://gist.github.com/kocsenc/10130261)
- [SpinRCP](http://lms.uni-mb.si/spinrcp/)

## Timeline editor

Cannot find it. It was at http://cm.bell-labs.com/cm/cs/what/timeedit/index.html

## Differences with PlusCal

- atomicity: Promela is fine grained; atomicity is at statement level and coarser gained atomicity is achieved with 
  dedicated statement grouping: ```atomic```, ```d_step```. 
  PlusCal is coarse grained: atomicity is in between labels; much harder to diagnose race conditions in the model.
- dead model code: Promela will warn about code that was not reached during verification as this could be a model flaw. 
  PlusCal needs to be told which code is essential.
- process termination: a process that did not end or did not end in an ```end``` label at the end of the verification 
  will be flagged as an error with Promela.
  PlusCal has no support for end-in-the-middle diagnostic labels or such.
- process creation: PlusCal cannot dynamically create processes from within your model.
- you can verify multiple temporal formulas at once with TLC but only one at a time with spin; although you can
  consider aggregating multiple LTL formulas into one until it becomes impossible to read it.
- no ```timeout``` equivalent in TLA+ to get out of a deadlock.
- fairness: PlusCal has weak & strong fairness builtin. 
  Spin has only weak fairness builtin; strong fairness has to be [defined](https://spinroot.com/fluxbb/viewtopic.php?id=671) via LTL/never claims.

As an [comparative example](https://accu.org/journals/overload/32/183/melinte/), here is the Dekker algorithm implemented in:
- [Promela](https://spinroot.com/spin/Man/Manual.html)
- [PlusCal](https://github.com/duerrfk/skp/blob/master/criticalsection5dekker/criticalsection5dekker.tla)

## Model

There are two models: [one for FSM and one for HSM](https://accu.org/journals/overload/33/186/melinte/). 

- FSM: 
  - There is at least one region in the state machine.
  - Each region executes in its own (promela) process.
  - A composite state executes in its own region - it has at
    least one region.
  - A simple state executes in the composite state/region 
    that owns it. 
- HSM:
  - each state executes in its own (promela) process.
  - non-canonical execution order: transition action(s), state 
    exit actions, state enter actions

- Events are asynchronous messages. Event names are unique per 
  plantuml file.
- State names are unique per plantuml file.

## Cheat Sheet

(just use [xspin/ispin.tcl](https://raw.githubusercontent.com/nimble-code/Spin/master/optional_gui/ispin.tcl) ). 

See also http://spinroot.com/spin/Man/4_SpinVerification.html

```
# simulation
# -i  interactive
spin pmlfile
```
```
#verification

# safety: assertions, non-reacheable code, race conditions, wrong end states, timout/deadlock + optional ltl
spin -a -f "![]ltl" > safety.ltl
spin -a -N safety.ltl pmlfile
gcc -DSAFETY -o pan pan.c
./pan

# acceptance (undesirable) cycles; -f / -DNFAIR: weak fairness
# "The accept label in this model formalizes the requirement that the second i
# state cannot persist forever, and cannot be revisited infinitely often either."
# -f optional weak fairness constraint
spin -a -f "!<>ltl" pmlfile
gcc -DNFAIR=numproc -o pan pan.c
./pan -a -f

# non-progress cycles/starvation
# -f optional weak fairness constraint
gcc -DNP -o pan pan.c
./pan -l -f
```
```
# error replay
# -p statements
# -g globals
# -l locals
# -s sent
# -r received
spin -t pmlfile
pan -t pmlfile
```
```
# reformat the model:
cat file | spin -pp | ...
```

```
@ slicing / model analysis
spin -A
```

## LTL
- ```[] P``` P should hold all the time: invariant; always
- ```<> P``` P should hold at lest once: guarantee; eventually
- ```p -> q``` ```(!p || q)``` implication. Note: true if p is false (!)
- ```p <-> q``` ```(p->q) && (q->p)``` equivalence
- ```[]<> P``` P should hold infinitely often or is the final state: progress
- ```<>[] P``` P should always hold sometime in the future or is the final state: stability
- ```[]((p) -> (<>(q)))``` response: p implies eventually q
- ```[]((p) -> ((q) U (r)))``` precedence: p implies q until r
- ```[]((p) -> <>((q) || (r)))``` objective
` ```(<>p) -> (<>q)``` correlation; order is not implied


## Various links
- [Implementing Statecharts in Promela/SPIN; Holzmann](https://www.researchgate.net/publication/2262971_Implementing_Statecharts_in_PromelaSPIN)
- [Spin & Promela](https://spinroot.com)
- [Tau](https://data.caltech.edu/records/8exsc-7h074)
- [Temporal Specification Patterns](https://matthewbdwyer.github.io/psp/)
- [Translating UML State Machine Diagram into Promela](https://www.iaeng.org/publication/IMECS2017/IMECS2017_pp512-516.pdf)
- [Total Store Ordering (TSO) and the Partial Store Ordering (PSO) memory models](https://github.com/plasklab/mmlib) & [usage](https://brilliantsugar.github.io/posts/how-i-learned-to-stop-worrying-and-love-juggling-c++-atomics/)

