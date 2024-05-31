#!/bin/bash

#
# 
#

./_upml.sh "../plantuml/switch/switch.plantuml" || exit 1
./_spin.sh "../plantuml/switch/switch.promela"
