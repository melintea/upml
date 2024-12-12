#!/bin/bash

#
# Usage: _test.sh file.plantuml
# Verify file is syntactically parseable
#
#set -x

echo "--- $1"

pumlfile="$1" 

#
#
#

tlafile="${pumlfile%.*}.tla"

./upml \
    --in "$pumlfile" \
    --backend tla \
    --out "$tlafile" \
    2>&1  || exit 1

tlahome=${HOME}/tla/toolbox
tlatoolbox=${tlahome}/toolbox
java -cp ${tlahome}/tla2tools.jar pcal.trans "$tlafile" 

#
#
#

spinfile="${pumlfile%.*}.promela"

./upml \
    --in "$pumlfile" \
    --backend spin \
    --out "$spinfile" \
    2>&1  || exit 1

exespin=${HOME}/work/Spin/Src/spin
rm pan.* _spin_nvr.tmp
${exespin} -a "$spinfile" || exit 1
if [[ ! -f pan.c ]]; then
    exit 1
fi
rm pan.* _spin_nvr.tmp

echo "---ok: $1"
