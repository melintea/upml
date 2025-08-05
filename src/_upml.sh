#!/bin/bash
#set -x

#
# Usage: _upml.sh --file file.plantuml --verify spin-fsm|spin-hsm|tla-hsm|both-fsm|both-hsm|none <--ide off> <--diff off>
#

gitroot=`git rev-parse --show-toplevel`
exeupml=${gitroot}/src/upml

#exespin=/usr/bin/spin
exespin=${HOME}/work/Spin/Src/spin
xexespin=${HOME}/work/Spin/optional_gui/ispin.tcl

tlahome=${HOME}/tla/toolbox
tlatoolbox=${tlahome}/toolbox

xdiffer=meld


echo "# ========================================================================"
echo "Usage: $0 --file file.plantuml --verify spin-fsm|spin-hsm|tla-hsm|both-fsm|both-hsm|none <--ide off> <--diff off>"
echo "[=== $@"


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

function generate_none() {
    ${exeupml} \
        --in "$pumlfile" \
        --backend none \
        2>&1  || exit 1
} # generate_none

function generate_tla_hsm() {
    ${exeupml} \
        --in "$pumlfile" \
        --backend tla-hsm \
        --out "$tlafile" \
        2>&1  || exit 1
} # generate_tla

function generate_tla_fsm() {
    ${exeupml} \
        --in "$pumlfile" \
        --backend tla-fsm \
        --out "$tlafile" \
        2>&1  || exit 1
} # generate_tla

function generate_spin_fsm() {
    ${exeupml} \
        --in "$pumlfile" \
        --backend spin-fsm \
        --out "$spinfile" \
        2>&1  || exit 1
} # generate_spin

function generate_spin_hsm() {
    ${exeupml} \
        --in "$pumlfile" \
        --backend spin-hsm \
        --out "$spinfile" \
        2>&1  || exit 1
} # generate_spin

function verify_tla() {
    echo "# -- tla -----------------------------------------------------------------"
    java -cp ${tlahome}/tla2tools.jar pcal.trans "$tlafile" || exit 1

    ## pluscal -> tla
    #java -cp ${tlahome}/tla2tools.jar pcal.trans "$*"

    ## verification
    #DEFAULT_JAVA_OPTS="-XX:+IgnoreUnrecognizedVMOptions -XX:+UseParallelGC"
    #if [ -z "$JAVA_OPTS" ]; then
    #  JAVA_OPTS="$DEFAULT_JAVA_OPTS"
    #fi
    #java $JAVA_OPTS -cp ${tlahome}/tla2tools.jar tlc2.TLC "$*"a
} # verify_tla

function spinit()
{
    echo "==== spin $*"
    ${exespin} $*
    echo "==== exit code: $?"
}

function verify_spin() {

    echo "# ------------------------------------------------------------------------"
    echo "#--- safety $spinfile"
    rm pan pan.* _spin_nvr.tmp *.trail
    ${exespin} -a "$spinfile" || exit 1
    if [[ ! -f pan.c ]]; then
        exit 1
    fi
    gcc -DMEMLIM=2048 -O2 -DXUSAFE -DSAFETY -w -o pan pan.c || exit 1
    ./pan -m10000 || exit 1
    errs=`./pan -m10000`
    if [ -z "$errs" ]; then
        echo "*** errors $errs"
        exit 1
    fi
    rm pan pan.* _spin_nvr.tmp *.trail

    echo "# ------------------------------------------------------------------------"
    echo "#--- acceptance + fairness (model is larger) $spinfile"
    ${exespin} -a "$spinfile" || exit 1
    if [[ ! -f pan.c ]]; then
        exit 1
    fi
    gcc -DMEMLIM=2048 -O2 -DNFAIR=4 -DXUSAFE -w -o pan pan.c || exit 1
    ./pan -m10000 -a || exit 1
    errs=`./pan -m10000 -a -f`
    if [ -z "$errs" ]; then
        echo "*** errors $errs"
        exit 1
    fi
    rm pan pan.* _spin_nvr.tmp *.trail

    echo "# ------------------------------------------------------------------------"
    echo "#--- non-progress $spinfile"
    ${exespin} -run -np "$spinfile" || exit 1
    rm pan pan.* _spin_nvr.tmp *.trail

    # -c columnated output
    # -g global vars
    #spinit -c -g -l -u400 "$spinfile"

    # -r print receive events
    # -s
    #spinit -r -s -u400 "$spinfile"

    # -p print all statements
    # -d symbol table
    # -C use of channels
    # -A warnings about useless statements
    #spinit -p -u400 "$spinfile"

    # spin -a $1
    # gcc -DBFS -DVERBOSE -o pan pan.c
    # gcc -DREACH -o pan pan.c
    # pan -i -m55
    # spin -p -t "$spinfile" # follow trail file

    # pan -D | dot -Tps | ps2pdf - pan.pdf
} # verify_spin



if [ x"${verify}" == xnone ]; then
    generate_none
fi

if [ x"${verify}" == "xspin-fsm" ] || [ x"${verify}" == "xboth-fsm" ]; then
    generate_spin_fsm
    verify_spin
    if [ x"${diff}" != xoff ]; then
        ${xdiffer} "$spinfile" &
    fi
    if [ x"${ide}" != xoff ] && [ -f "${xexespin}" ]; then
        ${xexespin} "$spinfile"&
        #exit 0
    fi
fi

if [ x"${verify}" == "xspin-hsm" ] || [ x"${verify}" == "xboth-hsm" ]; then
    generate_spin_hsm
    verify_spin
    if [ x"${diff}" != xoff ]; then
        ${xdiffer} "$spinfile" &
    fi
    if [ x"${ide}" != xoff ] && [ -f "${xexespin}" ]; then
        ${xexespin} "$spinfile"&
        #exit 0
    fi
fi

if [ x"${verify}" == "xtla-fsm" ] || [ x"${verify}" == "xboth-fsm" ]; then
    generate_tla_fsm
    verify_tla
    if [ x"${diff}" != xoff ]; then
        ${xdiffer} "$tlafile" &
    fi
    if [ x"${ide}" != xoff ]; then
        ${tlatoolbox} "$tlafile" &
    fi
fi

if [ x"${verify}" == "xtla-hsm" ] || [ x"${verify}" == "xboth-hsm" ]; then
    generate_tla_hsm
    verify_tla
    if [ x"${diff}" != xoff ]; then
        ${xdiffer} "$tlafile" &
    fi
    if [ x"${ide}" != xoff ]; then
        ${tlatoolbox} "$tlafile" &
    fi
fi

echo "]=== $pumlfile"
