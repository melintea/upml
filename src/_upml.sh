#!/bin/bash
set -x

#
# Usage: _upml.sh file.plantuml
#

pumlfile="$1" #"../plantuml/sip/sip.plantuml" #"$1"
spinfile="${pumlfile%.*}.promela"
tlafile="${pumlfile%.*}.tla"
#echo "$pumlfile => $spinfile" && exit 0

gitroot=`git rev-parse --show-toplevel`
exeupml=${gitroot}/src/upml

pushd ${gitroot}/src
make || exit 1
popd

${exeupml} \
    --in "$pumlfile" \
    --backend spin \
    --out "$spinfile" \
    2>&1  || exit 1
meld "$spinfile" &

${exeupml} \
    --in "$pumlfile" \
    --backend tla \
    --out "$tlafile" \
    2>&1  || exit 1
meld "$tlafile" &

