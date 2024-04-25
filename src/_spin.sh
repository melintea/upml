#!/bin/bash

#
#
#

function spinit()
{
    echo "==== spin $*"
    spin $*
}

spinit -c $1
spinit -r $1
spinit -p $1

# spin -a $1
# gcc -DBFS -o pan pan.c
# gcc -DREACH -o pan pan.c
# pan -i -m55
# spin -p -t $1 # follow trail file

# pan -D | dot -Tps | ps2pdf - pan.pdf

