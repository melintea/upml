- [Install](#install)
- [Various links](#various-links)

## Status

Not useable here.

Lean/Mathlib ships no LTL library, it has to be built by hand, especially the unbounded liveness always/eventually/until over an infinite EventStream.

## Install

See [the doc](https://github.com/leanprover/lean4/blob/master/doc/make/index.md)

```

sudo apt install build-essential cmake libgmp-dev libuv1-dev libssl-dev
git clone --depth 1 --single-branch --branch master https://github.com/leanprover/lean4.git
cd lean4
cmake --preset release
# OR: cmake --preset dev-release
...
# Current fail:
 Failed to clone repository: 'https://github.com/microsoft/mimalloc'

# Next possible steps:
make -C build/release -j$(nproc || sysctl -n hw.logicalcpu)

# https://github.com/leanprover/lean4/blob/master/doc/dev/index.md#dev-setup-using-elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain none

```

## Various links
- [Documentation](https://lean-lang.org/learn/)

