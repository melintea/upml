#!/bin/bash

#
# 
#

./_upml.sh "../plantuml/sip/sip.plantuml" || exit 1
./_spin.sh "../plantuml/sip/sip.promela"
