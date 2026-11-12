#!/usr/bin/env bash
# Translate the adapted original core and compile the resulting Rocq definitions.
set -euo pipefail
rocq_bin=${1:?Usage: translate.sh ROCQ_BIN_DIRECTORY}
project=$(git rev-parse --show-toplevel)
cd "$project"
experiment="$project/experiments/generator-haskell"
build="$project/build/generator-haskell"
source="$build/hs-to-rocq-5e6a7bddfa02b818a9e8490ed107b11bd52a84e4"
base="$source/examples/rocq9.0/base"
output="$build/translated"
mkdir -p "$output"
exec > >(tee "$build/translation.log") 2>&1
rm -f "$output/Generator.vo" "$output/Generator.vos" "$output/Generator.vok"
export PATH="$build/ghc-9.10.3-x86_64-unknown-linux/bin:$rocq_bin:$PATH"
# A module skip also suppresses the source's derived Eq instance. Dependencies
# remain external because this translation uses --nonrecursive.
sed '/^skip module GHC.Classes$/d' "$source/base/edits" > "$build/base-edits"
"$build/bin/hs-to-rocq" --target-version 9.0 --strict --nonrecursive \
  -e "$build/base-edits" -e "$experiment/edits" \
  --iface-dir "$base" --import-dir "$experiment/src" \
  --preamble "$experiment/rocq/preamble.v" \
  "$experiment/src/Generator.hs" -o "$output"
if rg -n 'Admitted|Admit Obligations|Axiom|deferredFix|Unset Guard Checking' "$output/Generator.v"; then
  echo 'Translation contains unsupported assumptions or disabled termination checking' >&2
  exit 1
fi
cp "$experiment/rocq/Word64Bridge.v" "$output/Word64Bridge.v"
cp "$experiment/rocq/SequenceBridge.v" "$output/SequenceBridge.v"
coqc -Q "$base" '' -Q "$output" '' "$output/Word64Bridge.v"
coqc -Q "$base" '' -Q "$output" '' "$output/SequenceBridge.v"
coqc -Q "$base" '' -Q "$output" '' "$output/Generator.v"
