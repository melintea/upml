#!/bin/bash

#
# 
#

./_upml.sh "../plantuml/sip/sip.plantuml" || exit 1
./_tla.sh  "../plantuml/sip/sip.tla"
