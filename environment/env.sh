#!/usr/bin/env bash
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
switch="$root/_opam-testing-theorems"
context="$switch/testing-theorems-artifact-context"
archive="$switch/testing-theorems-artifact-context.tar.gz"
archive_sha=876e30bf41477f9a90077e3876df08555c77b624b35e11508500f4ae01e7035a
coverage_toolchain=nightly-2026-11-21
coverage_rust_commit=c7d5ba59d8e11ee2e2204b173458eec4cb41c973
action=${1:-coqtop}
if [[ $# -gt 0 ]]; then shift; fi

case "$action" in
  setup)
    mkdir -p "$switch"
    if [[ ! -f "$archive" ]]; then
      # The source context precedes the 2 GB Docker image in the official archive.
      # Read only this member, and verify its independently recorded digest.
      python3 - "$archive" <<'PY'
import pathlib, shutil, sys, tarfile, urllib.request
url = 'https://zenodo.org/records/22087774/files/testing-theorems-final-submission.tar.gz?download=1'
destination = pathlib.Path(sys.argv[1])
partial = destination.with_suffix('.partial')
try:
    with urllib.request.urlopen(url, timeout=120) as response, tarfile.open(fileobj=response, mode='r|gz') as outer:
        for member in outer:
            if member.name.endswith('/testing-theorems-artifact-context.tar.gz'):
                with outer.extractfile(member) as source, partial.open('wb') as target:
                    shutil.copyfileobj(source, target)
                partial.replace(destination)
                break
        else:
            raise SystemExit('Official artifact has no source context archive')
finally:
    partial.unlink(missing_ok=True)
PY
    fi
    printf '%s  %s\n' "$archive_sha" "$archive" | sha256sum --check
    if [[ ! -d "$context" ]]; then
      tar -xzf "$archive" -C "$switch"
    fi
    if ! opam repository list --all --short | grep -qx rocq-released; then
      opam repository add rocq-released https://rocq-prover.org/opam/released --dont-select --yes
    fi
    if [[ ! -d "$switch/_opam" ]]; then
      opam switch create "$switch" --empty --repos=rocq-released,default --no-switch --yes
    fi
    opam switch import "$root/environment/opam-switch.export" --switch="$switch" --yes --jobs="${JOBS:-8}"
    # Match the artifact Dockerfile: paper examples are compiled explicitly below.
    while IFS= read -r -d '' dune_file; do
      mv "$dune_file" "$dune_file.artifact-disabled"
    done < <(find "$context/QuickChick/examples/paper-tests" -name dune -print0)
    opam pin add coq-quickchick.dev "$context/QuickChick" --switch="$switch" --no-action --yes
    opam install coq-quickchick --switch="$switch" --yes --jobs="${JOBS:-8}"
    opam exec --switch="$switch" --set-switch -- coqc --version
    ;;
  setup-cedar)
    if [[ ! -d "$context/cedar-server" ]]; then
      echo 'Run bash environment/env.sh setup first.' >&2
      exit 1
    fi
    export CARGO_HOME="$switch/cargo" RUSTUP_HOME="$switch/rustup"
    if [[ ! -x "$CARGO_HOME/bin/cargo" ]]; then
      curl --fail --location --retry 3 https://static.rust-lang.org/rustup/dist/x86_64-unknown-linux-gnu/rustup-init -o "$switch/rustup-init"
      chmod +x "$switch/rustup-init"
      "$switch/rustup-init" -y --profile minimal --default-toolchain nightly --no-modify-path
    fi
    cd "$context/cedar-server"
    "$CARGO_HOME/bin/cargo" build --release --locked -j "${JOBS:-8}"
    ;;
  setup-cedar-coverage)
    # Separate build: preserve the original artifact binary and all old evidence.
    export CARGO_HOME="$switch/cargo" RUSTUP_HOME="$switch/rustup"
    export PATH="$CARGO_HOME/bin:$PATH"
    "$CARGO_HOME/bin/rustup" toolchain install "$coverage_toolchain" --profile minimal --component llvm-tools-preview
    export RUSTUP_TOOLCHAIN="$coverage_toolchain"
    actual_commit=$("$CARGO_HOME/bin/rustc" -Vv | sed -n 's/^commit-hash: //p')
    [[ "$actual_commit" == "$coverage_rust_commit" ]] || { echo 'Coverage compiler commit mismatch' >&2; exit 1; }
    export CARGO_TARGET_DIR="$switch/cedar-coverage-target"
    export RUSTFLAGS='-C instrument-coverage -Z coverage-options=branch -C debuginfo=2'
    cd "$context/cedar-server"
    "$CARGO_HOME/bin/cargo" build --locked --offline -j "${JOBS:-8}"
    ;;
  cedar-rust)
    export CARGO_HOME="$switch/cargo" RUSTUP_HOME="$switch/rustup"
    export PATH="$CARGO_HOME/bin:$PATH"
    export RUSTUP_TOOLCHAIN="$coverage_toolchain"
    actual_commit=$("$CARGO_HOME/bin/rustc" -Vv | sed -n 's/^commit-hash: //p')
    [[ "$actual_commit" == "$coverage_rust_commit" ]] || { echo 'Run setup-cedar-coverage: pinned compiler unavailable' >&2; exit 1; }
    exec "$@"
    ;;
  check)
    mkdir -p "$switch/checks"
    run=$(mktemp -d "$switch/checks/verification.XXXXXXXX")
    cp "$root/example.v" "$root"/environment/checks/*.v "$run/"
    cd "$run"
    opam exec --switch="$switch" --set-switch -- coqc --version > versions.log
    opam list --switch="$switch" --installed --columns=name,version >> versions.log
    for file in *.v; do
      if ! opam exec --switch="$switch" --set-switch -- coqc "$file" > "${file%.v}.log" 2>&1; then
        tail -n 60 "${file%.v}.log" >&2
        exit 1
      fi
      # coqc can exit successfully even if QuickChick found a counterexample.
      if ! grep -F '+++ Passed 10000 tests (0 discards)' "${file%.v}.log"; then
        tail -n 60 "${file%.v}.log" >&2
        exit 1
      fi
      opam exec --switch="$switch" --set-switch -- coqchk -silent "${file%.v}" > "${file%.v}.kernel.log" 2>&1
    done
    printf 'Verified derivation, execution, and kernel checks: %s\n' "$run"
    ;;
  check-cedar)
    mkdir -p "$switch/checks"
    run=$(mktemp -d "$switch/checks/cedar.XXXXXXXX")
    export RESULTS_DIR="$run" CEDAR_PIPE_DIR="$run/pipes" RUN_REPROS=0
    export CEDAR_SERVER="$context/cedar-server/target/release/cedar-server"
    opam exec --switch="$switch" --set-switch -- bash "$context/QuickChick/examples/paper-tests/cedar/run_cedar_case_study.sh"
    if ! grep -E '\+\+\+ Passed|\*\*\* Failed|\*\*\* Gave up' "$run/cedar_quickchick.log"; then
      echo "No completed QuickChick result: $run" >&2
      exit 1
    fi
    ;;
  *)
    if [[ ! -x "$switch/_opam/bin/coqc" ]]; then
      echo 'Run bash environment/env.sh setup first.' >&2
      exit 1
    fi
    exec opam exec --switch="$switch" --set-switch -- "$action" "$@"
    ;;
esac
