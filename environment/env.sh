#!/usr/bin/env bash
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
state="$root/_opam-testing-theorems"
coq_switch="$state/coq-switch"
frontend_switch="$state/frontend-switch"
context="$state/sources/testing-theorems-artifact-context"
archive="$state/sources/testing-theorems-artifact-context.tar.gz"
archive_sha=876e30bf41477f9a90077e3876df08555c77b624b35e11508500f4ae01e7035a
frontend_source="$state/sources/p4-spectec"
action=${1:-coqtop}
if [[ $# -gt 0 ]]; then shift; fi
# All opam state, including initialization and temporary/cache files, is local.
export OPAMROOT="$state/opam-root" OPAMLOGS="$state/logs/opam"
export TMPDIR="$state/tmp" XDG_CACHE_HOME="$state/cache"
export OPAMJOBS="${JOBS:-2}"
unset OPAMSWITCH OPAM_SWITCH_PREFIX
mkdir -p "$OPAMROOT" "$OPAMLOGS" "$TMPDIR" "$XDG_CACHE_HOME" "$state/sources" "$state/build" "$state/logs"
opam_root() { local command=$1; shift; opam "$command" --root="$OPAMROOT" "$@"; }
opam_coq() { local command=$1; shift; opam "$command" --root="$OPAMROOT" --switch="$coq_switch" "$@"; }
opam_frontend() { local command=$1; shift; opam "$command" --root="$OPAMROOT" --switch="$frontend_switch" "$@"; }
initialize_root() {
  if [[ ! -f "$OPAMROOT/config" ]]; then
    # Container kernels may forbid user namespaces. Disable sandboxing ONLY in
    # this dedicated root; the calling environment controls command isolation.
    opam_root init --bare --no-setup --disable-shell-hook --disable-sandboxing --yes
  fi
}
start_log() {
  local log
  log=$(mktemp "$state/logs/${action}.XXXXXXXX.log")
  exec > >(tee "$log") 2>&1
  printf 'Log: %s\nOPAMROOT: %s\nCoq switch: %s\nFrontend switch: %s\n' "$log" "$OPAMROOT" "$coq_switch" "$frontend_switch"
}
require_coq() {
  if [[ ! -x "$coq_switch/_opam/bin/coqc" ]]; then
    echo 'Run bash environment/env.sh setup first.' >&2; exit 1
  fi
}
case "$action" in
  setup)
    start_log
    initialize_root
    if [[ ! -f "$archive" ]]; then
      # Stream the small source member before the 2 GB Docker image, then
      # verify its independently recorded digest before extraction.
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
    if [[ ! -d "$context" ]]; then tar -xzf "$archive" -C "$state/sources"; fi
    if ! opam_root repository list --all --short | grep -qx rocq-released; then
      opam_root repository add rocq-released https://rocq-prover.org/opam/released --dont-select --yes
    fi
    if [[ ! -d "$coq_switch/_opam" ]]; then
      opam_root switch create "$coq_switch" --empty --repos=rocq-released,default --no-switch --yes
    fi
    opam_coq switch import "$root/environment/opam-switch.export" --yes --jobs="$OPAMJOBS"
    # Match the official Dockerfile: paper examples are checked explicitly.
    while IFS= read -r -d '' dune_file; do
      mv "$dune_file" "$dune_file.artifact-disabled"
    done < <(find "$context/QuickChick/examples/paper-tests" -name dune -print0)
    opam_coq pin add coq-quickchick.dev "$context/QuickChick" --no-action --yes
    opam_coq install coq-quickchick --yes --jobs="$OPAMJOBS"
    coq_version=$(opam_coq exec --set-switch -- coqc --version)
    printf '%s\n' "$coq_version"
    grep -F 'version 8.20.0' <<< "$coq_version"
    [[ $(opam_coq exec --set-switch -- ocamlc -version) == 4.14.2 ]]
    ;;
  setup-frontend)
    start_log
    initialize_root
    if [[ ! -f "$frontend_source/dune-project" ]]; then
      echo "Pinned frontend source missing: $frontend_source/dune-project" >&2; exit 1
    fi
    if [[ ! -d "$frontend_switch/_opam" ]]; then
      opam_root switch create "$frontend_switch" ocaml-base-compiler.5.1.1 --repos=default --no-switch --yes --jobs="$OPAMJOBS"
    fi
    if [[ ! -x "$frontend_switch/_opam/bin/dune" ]]; then
      opam_frontend install dune.3.21.1 --yes --jobs="$OPAMJOBS"
    fi
    # This pinned revision generates its opam file from dune-project. Generate
    # only that metadata in a fresh build directory, preserving source inputs.
    dependencies=$(mktemp -d "$state/build/frontend-dependencies.XXXXXXXX")
    cp "$frontend_source/dune-project" "$dependencies/"
    opam_frontend exec --set-switch -- dune build --root "$dependencies" p4spectec.opam
    opam_frontend install "$dependencies/p4spectec.opam" --deps-only --yes --jobs="$OPAMJOBS"
    opam_frontend switch export "$dependencies/installed.export" --full
    frontend_version=$(opam_frontend exec --set-switch -- ocamlc -version)
    printf '%s\n' "$frontend_version"
    [[ "$frontend_version" == 5.1.1 ]]
    ;;
  frontend)
    if [[ ! -x "$frontend_switch/_opam/bin/ocamlc" ]]; then
      echo 'Run bash environment/env.sh setup-frontend first.' >&2; exit 1
    fi
    exec opam exec --root="$OPAMROOT" --switch="$frontend_switch" --set-switch -- "$@"
    ;;
  check)
    start_log
    require_coq
    mkdir -p "$state/checks"
    run=$(mktemp -d "$state/checks/verification.XXXXXXXX")
    cp "$root"/environment/checks/*.v "$run/"
    cd "$run"
    opam_coq exec --set-switch -- coqc --version > versions.log
    grep -F 'version 8.20.0' versions.log
    coq_ocaml_version=$(opam_coq exec --set-switch -- ocamlc -version)
    printf '%s\n' "$coq_ocaml_version" >> versions.log
    [[ "$coq_ocaml_version" == 4.14.2 ]]
    opam_coq list --installed --columns=name,version >> versions.log
    for file in *.v; do
      if ! opam_coq exec --set-switch -- coqc "$file" > "${file%.v}.log" 2>&1; then
        tail -n 60 "${file%.v}.log" >&2; exit 1
      fi
      # QuickChick counterexamples do not necessarily make coqc exit nonzero.
      if ! grep -F '+++ Passed 10000 tests (0 discards)' "${file%.v}.log"; then
        tail -n 60 "${file%.v}.log" >&2; exit 1
      fi
      opam_coq exec --set-switch -- coqchk -silent "${file%.v}" > "${file%.v}.kernel.log" 2>&1
    done
    printf 'Verified derivation, execution, and kernel checks: %s\n' "$run"
    ;;
  *)
    require_coq
    exec opam exec --root="$OPAMROOT" --switch="$coq_switch" --set-switch -- "$action" "$@"
    ;;
esac
