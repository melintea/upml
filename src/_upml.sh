#!/bin/bash

#
# Usage: _upml.sh file.plantuml
#

pumlfile="$1" #"../plantuml/sip/sip.plantuml" #"$1"
spinfile="${pumlfile%.*}.promela"
#echo "$pumlfile => $spinfile" && exit 0

make || exit 1

./upml \
    --in "$pumlfile" \
    --backend spin \
    --out "$spinfile" \
    2>&1
