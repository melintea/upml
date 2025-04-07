#!/bin/bash
#set -x

exespin=${HOME}/work/Spin/Src/spin
xexespin=${HOME}/work/Spin/optional_gui/ispin.tcl
xdiffer=meld
spinfile=trace.promela

#rm *.trail
${xexespin} "$spinfile"&
#${xdiffer} "$spinfile" &

# safety
rm pan pan.* _spin_nvr.tmp *.trail
${exespin} -a "$spinfile" || exit 1
if [[ ! -f pan.c ]]; then
    exit 1
fi
gcc -DMEMLIM=1024 -O2 -DXUSAFE -DSAFETY -w -o pan pan.c || exit 1
./pan -m10000 || exit 1
rm pan pan.* _spin_nvr.tmp *.trail

# acceptance
${exespin} -a "$spinfile" || exit 1
if [[ ! -f pan.c ]]; then
    exit 1
fi
gcc -DMEMLIM=1024 -O2 -DXUSAFE -w -o pan pan.c || exit 1
./pan -m10000 -a || exit 1
rm pan pan.* _spin_nvr.tmp *.trail

printf "\e[42m*** Pass ***\e[0m \n"

