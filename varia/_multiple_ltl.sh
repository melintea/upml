#!/bin/bash

# Usage: $0 test.pml

# TODO
# See https://stackoverflow.com/questions/45703760/testing-multiple-ltl-formulae-with-spin


function set_trail_name()
{
    sed -i "s/^\\(char \\*TrailFile =\\)\\(.*\\)$/\\1 \"${1}\";/" "${2}";
}

function check_property()
{
    echo -e "\\n>>> Testing property ${1} ...\\n"

    set_trail_name "${1}" pan.c
    gcc -o pan pan.c
    ./pan -a -N "${1}"
}

function check_properties()
{
    set -e

    spin -a "${1}" 1>/dev/null
    mapfile -t properties < <(gawk 'match($0, /^ltl ([^{]+) .*$/, a) { print a[1] }' "${1}")

    for prop in "${properties[@]}"
    do
        check_property "${prop}"
    done

    set +e
}

check_properties "${@}"

