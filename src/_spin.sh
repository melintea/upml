#!/bin/bash

#
# Usage: _spin.sh file.promela
#

#exespin=/usr/bin/spin
exespin=${HOME}/work/Spin/Src/spin
xexespin=${HOME}/work/Spin/optional_gui/ispin.tcl


function spinit()
{
    echo "==== spin $*"
    ${exespin} $*
}

${xexespin} $1&
spinit -c $1
spinit -r $1
spinit -p $1

# spin -a $1
# gcc -DBFS -o pan pan.c
# gcc -DREACH -o pan pan.c
# pan -i -m55
# spin -p -t $1 # follow trail file

# pan -D | dot -Tps | ps2pdf - pan.pdf

