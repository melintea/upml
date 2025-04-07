#!/bin/bash
#set -x

xexespin=${HOME}/work/Spin/optional_gui/ispin.tcl
xdiffer=meld
spinfile=trace.promela

rm *.trail
${xexespin} "$spinfile"&
#${xdiffer} "$spinfile" &
