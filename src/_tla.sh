#!/bin/bash

#
# Usage: _tla.sh file.tla
#

#meld ../tla/switch.toolbox/Model_1/switch.tla ../plantuml/switch/switch.ref.tla &

tlatoolbox=${HOME}/tla/toolbox/toolbox

${tlatoolbox} $* &

## pluscal -> tla
#java -cp PREFIX/lib/tla2tools.jar pcal.trans "$*"

## verification
#DEFAULT_JAVA_OPTS="-XX:+IgnoreUnrecognizedVMOptions -XX:+UseParallelGC"
#if [ -z "$JAVA_OPTS" ]; then
#  JAVA_OPTS="$DEFAULT_JAVA_OPTS"
#fi
#java $JAVA_OPTS -cp PREFIX/lib/tla2tools.jar tlc2.TLC "$*"a

