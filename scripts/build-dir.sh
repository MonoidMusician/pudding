#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname "$0")/.."

# Should be something like
# dist-newstyle/build/x86_64-linux/ghc-9.8.4/pudding-0.1.0.0/x/pudding/noopt/build/pudding/pudding
# where the /noopt segment is optional
# (see optimization: False in cabal.project)
BIN_PATH="$(cabal list-bin pudding)"
BIN_PATH="$(realpath -s --relative-to="$PWD" -- "$BIN_PATH")"
BUILD_DIR="$(
    echo "$BIN_PATH" | grep -oE ".+/pudding-[0-9]+\.[0-9]+\.[0-9]+\.[0-9]+"
)$(
    echo "$BIN_PATH" | grep -oE "/noopt\b" || true
)"
echo "$BUILD_DIR"
ln -sf --no-dereference -- "$BUILD_DIR" build-dir
