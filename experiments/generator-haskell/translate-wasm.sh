#!/usr/bin/env bash
# Translate the actual pure Wasm module generator and compile generated Rocq.
set -euo pipefail
rocq_bin=${1:?Usage: translate-wasm.sh ROCQ_BIN_DIRECTORY}
project=$(git rev-parse --show-toplevel)
cd "$project"
experiment="$project/experiments/generator-haskell"
build="$project/build/generator-haskell"
source="$build/hs-to-rocq-5e6a7bddfa02b818a9e8490ed107b11bd52a84e4"
base="$source/examples/rocq9.0/base"
output="$build/translated"
mkdir -p "$output"
exec > >(tee "$build/wasm-translation.log") 2>&1
export PATH="$build/ghc-9.10.3-x86_64-unknown-linux/bin:$rocq_bin:$PATH"
sed '/^skip module GHC.Classes$/d' "$source/base/edits" > "$build/base-edits"
"$build/bin/hs-to-rocq" --target-version 9.0 --strict --nonrecursive \
  -e "$build/base-edits" -e "$experiment/wasm.edits" \
  --iface-dir "$base" --iface-dir "$output" --import-dir "$experiment/src" \
  --preamble "$experiment/rocq/wasm-preamble.v" \
  "$experiment/src/WasmGenerator.hs" -o "$output"
if rg -n 'Admitted|Admit Obligations|Axiom|deferredFix|Unset Guard Checking' "$output/WasmGenerator.v"; then
  echo 'Translation contains unsupported assumptions or disabled termination checking' >&2
  exit 1
fi
coqc -Q "$base" '' -Q "$output" '' "$output/WasmGenerator.v"
