#!/usr/bin/env bash
# Build `charon` and `charon-driver` with profile-guided optimization (PGO).
#
# Usage: scripts/build-pgo.sh <training command...>
#
# Builds an instrumented charon, runs the training command with `$CHARON` set to it, then builds
# charon into `charon/target/release` optimized for the recorded profile. Train on inputs like the
# ones charon will run on: a profile of unrepresentative runs (e.g. the ui tests) makes charon slower.
# Example:
#   scripts/build-pgo.sh sh -c 'cd ~/my-crate && "$CHARON" cargo --preset aeneas'
#
# Profiles can't be reused across builds: they are keyed by symbol names, which change with the
# version of charon, its dependencies, the toolchain and the codegen settings.
set -euo pipefail
if [ $# -eq 0 ]; then
    sed -n '2,13p' "$0"
    exit 1
fi
orig=$PWD
cd "$(dirname "$0")/../charon"
host=$(rustc -vV | sed -n 's/^host: //p')
profdata="$(rustc --print sysroot)/lib/rustlib/$host/bin/llvm-profdata"
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT

# Both builds must be the same cargo command, so that symbol names match: `RUSTFLAGS` doesn't
# affect them.
build() {
    cargo build --release --bin charon --bin charon-driver
}
RUSTFLAGS="${RUSTFLAGS:-} -Cprofile-generate=$dir/build" CARGO_TARGET_DIR=target/pgo-instrumented build
instrumented=$PWD/target/pgo-instrumented/release/charon
(cd "$orig" && CHARON=$instrumented LLVM_PROFILE_FILE="$dir/train/%8m.profraw" "$@")
"$profdata" merge --sparse -o "$dir/charon.profdata" "$dir/train"
RUSTFLAGS="${RUSTFLAGS:-} -Cprofile-use=$dir/charon.profdata" build
