#!/usr/bin/env bash
# Reproduce the unadapted core's translation boundary without filling obligations.
set -euo pipefail
rocq_bin=${1:?Usage: translate-original.sh ROCQ_BIN_DIRECTORY}
project=$(git rev-parse --show-toplevel)
cd "$project"
experiment="$project/experiments/generator-haskell"
build="$project/build/generator-haskell"
source="$build/hs-to-rocq-5e6a7bddfa02b818a9e8490ed107b11bd52a84e4"
base="$source/examples/rocq9.0/base"
output="$build/original-translation"
mkdir -p "$output"
exec > >(tee "$build/original-translation.log") 2>&1
rm -f "$output/Generator.vo" "$output/Generator.vos" "$output/Generator.vok"
export PATH="$build/ghc-9.10.3-x86_64-unknown-linux/bin:$rocq_bin:$PATH"
"$build/bin/hs-to-rocq" --target-version 9.0 --strict --nonrecursive \
  -e "$source/base/edits" -e "$experiment/original.edits" \
  --iface-dir "$base" --import-dir "$experiment/original" \
  "$experiment/original/Generator.hs" -o "$output"
coqc -Q "$base" '' -Q "$output" '' "$output/Generator.v"
