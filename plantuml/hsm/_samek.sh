#!/bin/bash

clear
pushd ../../src
#make test || exit 1
make || exit 1
popd

../../src/upml --in samek.plantuml --backend spin-hsm | tee samek.promela

rm *.tmp *.trail
xexespin=${HOME}/work/Spin/optional_gui/ispin.tcl
${xexespin} samek.promela &

../_plantuml.sh samek.plantuml&
#lximage-qt ./samek.png &
nedit ./samek.promela &
nedit ./samek.promela &

