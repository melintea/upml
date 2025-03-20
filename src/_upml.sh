#!/bin/bash
#set -x

#
# Usage: _upml.sh --file file.plantuml --verify spin|tla|both
#

gitroot=`git rev-parse --show-toplevel`
exeupml=${gitroot}/src/upml

#exespin=/usr/bin/spin
exespin=${HOME}/work/Spin/Src/spin
xexespin=${HOME}/work/Spin/optional_gui/ispin.tcl

tlahome=${HOME}/tla/toolbox
tlatoolbox=${tlahome}/toolbox

echo "Usage: $0 --file file.plantuml --verify spin|tla|both"

while [ $# -gt 0 ]; do
    if [[ $1 == *"--"* ]]; then
        v="${1/--/}"
        declare $v="$2"
    fi
    shift
done

pumlfile="$file" #"../plantuml/sip/sip.plantuml"
spinfile="${pumlfile%.*}.promela"
tlafile="${pumlfile%.*}.tla"

if [ x"${pumlfile}" == x ]; then
    echo "Must specify --file"
    exit 1
fi
pumlfile=`realpath ${pumlfile}`

pushd ${gitroot}/src
make || exit 1
popd

function generate_tla() {
    ${exeupml} \
        --in "$pumlfile" \
        --backend tla \
        --out "$tlafile" \
        2>&1  || exit 1
    meld "$tlafile" &
} # generate_tla

function generate_spin() {
    ${exeupml} \
        --in "$pumlfile" \
        --backend spin \
        --out "$spinfile" \
        2>&1  || exit 1
    meld "$spinfile" &
} # generate_spin

function verify_tla() {
    java -cp ${tlahome}/tla2tools.jar pcal.trans "$tlafile" || exit 1
    #${tlatoolbox} "$tlafile" &

    ## pluscal -> tla
    #java -cp ${tlahome}/tla2tools.jar pcal.trans "$*"

    ## verification
    #DEFAULT_JAVA_OPTS="-XX:+IgnoreUnrecognizedVMOptions -XX:+UseParallelGC"
    #if [ -z "$JAVA_OPTS" ]; then
    #  JAVA_OPTS="$DEFAULT_JAVA_OPTS"
    #fi
    #java $JAVA_OPTS -cp ${tlahome}/tla2tools.jar tlc2.TLC "$*"a
} # test_tla

function spinit()
{
    echo "==== spin $*"
    ${exespin} $*
    echo "==== exit code: $?"
}

function verify_spin() {
    if [ -f "${xexespin}" ]; then
        ${xexespin} "$spinfile"&
        #exit 0
    fi

    # -c columnated output
    # -g global vars
    spinit -c -g -l -u400 "$spinfile"

    # -r print receive events
    # -s
    spinit -r -s -u400 "$spinfile"

    # -p print all statements
    # -d symbol table
    # -C use of channels
    # -A warnings about useless statements
    spinit -p -u400 "$spinfile"

    # spin -a $1
    # gcc -DBFS -DVERBOSE -o pan pan.c
    # gcc -DREACH -o pan pan.c
    # pan -i -m55
    # spin -p -t "$spinfile" # follow trail file

    # pan -D | dot -Tps | ps2pdf - pan.pdf

    # acceptance: pan -a
} # test_spin


generate_spin
if [ x"${verify}" == xspin ] || [ x"${verify}" == xboth ]; then
    verify_spin
fi

generate_tla
if [ x"${verify}" == xtla ] || [ x"${verify}" == xboth ]; then
    verify_tla
fi

