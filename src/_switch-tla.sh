#!/bin/bash

#
# 
#

./_upml.sh "../plantuml/switch/switch.plantuml" || exit 1
./_tla.sh  "../plantuml/switch/switch.tla"
