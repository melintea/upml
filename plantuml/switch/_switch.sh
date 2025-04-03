#!/bin/bash

#
# 
#

gitroot=`git rev-parse --show-toplevel`
shupml=${gitroot}/src/_upml.sh

${shupml} --file "../plantuml/switch/switch.plantuml" --verify spin
