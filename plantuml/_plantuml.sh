#!/bin/sh

#
#
#

plantuml   $1 || exit 1
lximage-qt ${1%.*}.png &
