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

if [ -f "${xexespin}" ]; then
    ${xexespin} $1&
    #exit 0
fi

# -c columnated output
# -g global vars
spinit -c -g -l -u200 $1

# -r print receive events
# -s
spinit -r -s -u200 $1

# -p print all statements
# -d symbol table
# -C use of channels
# -A warnings about useless statements
spinit -p -u200 $1

# spin -a $1
# gcc -DBFS -DVERBOSE -o pan pan.c
# gcc -DREACH -o pan pan.c
# pan -i -m55
# spin -p -t $1 # follow trail file

# pan -D | dot -Tps | ps2pdf - pan.pdf

# acceptance: pan -a


