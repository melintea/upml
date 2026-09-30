- [Install](#install)
- [Various links](#various-links)

## Status

WIP. 

## Install

See [the doc](https://github.com/leanprover/lean4/blob/master/doc/make/index.md)

```

git clone https://github.com/leanprover/lean4
cd lean4
cmake --preset release
make -C build/release -j$(nproc || sysctl -n hw.logicalcpu)

# https://github.com/leanprover/lean4/blob/master/doc/dev/index.md#dev-setup-using-elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain none

```

## Various links
- [Documentation](https://lean-lang.org/learn/)

