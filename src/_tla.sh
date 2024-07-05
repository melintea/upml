#!/bin/bash

#
# Usage: _tla.sh file.tla
#

tlatoolbox=${HOME}/tla/toolbox/toolbox

meld ../tla/switch.toolbox/Model_1/switch.tla ../plantuml/switch/switch.ref.tla &

${tlatoolbox} $* &

