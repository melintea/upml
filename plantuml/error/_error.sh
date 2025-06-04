#!/bin/bash

clear && make || exit 1

gitroot=`git rev-parse --show-toplevel`
shupml=${gitroot}/src/_upml.sh

${shupml} --file "../plantuml/fsm/error/sip.plantuml" --verify spin

