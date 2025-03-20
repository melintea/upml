#!/bin/bash

#
# 
#

gitroot=`git rev-parse --show-toplevel`
shupml=${gitroot}/src/_upml.sh

${shupml} --file "../plantuml/hsm/hsm2.plantuml" --verify spin
