#!/bin/bash

clear && make || exit 1

gitroot=`git rev-parse --show-toplevel`
shupml=${gitroot}/src/upml

echo "== A file with a synthax error"
${shupml} --in "../plantuml/error/sip.plantuml" 
echo "== Exit code: $?"

