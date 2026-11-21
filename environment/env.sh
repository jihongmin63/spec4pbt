#!/usr/bin/env bash
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
switch="$root/_opam-popl18"
action=${1:-coqtop}
if [[ $# -gt 0 ]]; then shift; fi

if [[ "$action" != setup && ! -x "$switch/_opam/bin/coqc" ]]; then
  echo 'Run bash environment/env.sh setup first.' >&2
  exit 1
fi

# OCaml 4.05 predates C23. Generate compatibility wrappers beside the install.
mkdir -p "$switch/c-compat"
cat > "$switch/c-compat/gcc" <<'EOF'
#!/bin/sh
exec /usr/bin/gcc -std=gnu11 -Wno-implicit-function-declaration "$@"
EOF
chmod +x "$switch/c-compat/gcc"
ln -sfn gcc "$switch/c-compat/cc"
export PATH="$switch/c-compat:$PATH"

case "$action" in
  setup)
    if ! opam repository list --all --short | grep -qx rocq-released; then
      opam repository add rocq-released https://rocq-prover.org/opam/released --dont-select --yes
    fi
    if ! opam repository list --all --short | grep -qx opam-archive; then
      opam repository add opam-archive git+https://github.com/ocaml/opam-repository-archive.git --dont-select --yes
    fi
    if [[ ! -d "$switch/_opam" ]]; then
      opam switch create "$switch" --empty --repos=rocq-released,default,opam-archive --no-switch --yes
    fi
    opam repository set-repos rocq-released default opam-archive --switch="$switch"
    # Includes the pinned QuickChick source, checksum, and package metadata.
    opam switch import "$root/environment/opam-switch.export" --switch="$switch" --yes --jobs="${JOBS:-8}"
    opam exec --switch="$switch" -- coqc --version
    ;;
  check)
    mkdir -p "$switch/checks"
    run=$(mktemp -d "$switch/checks/verification.XXXXXXXX")
    cp "$root/example.v" "$run/"
    cd "$run"
    opam exec --switch="$switch" -- coqc --version | tee versions.log
    opam list --switch="$switch" --installed --columns=name,version >> versions.log
    if ! opam exec --switch="$switch" -- coqc example.v > compile.log 2>&1; then
      tail -n 60 compile.log >&2
      exit 1
    fi
    # QuickChick can report failure without making coqc fail.
    if ! grep -F '+++ Passed 10000 tests (0 discards)' compile.log; then
      tail -n 60 compile.log >&2
      exit 1
    fi
    opam exec --switch="$switch" -- coqchk -silent example 2>&1 | tee kernel-check.log
    printf 'Verified generator, generated proof, execution, and kernel check: %s\n' "$run"
    ;;
  *) exec opam exec --switch="$switch" --set-switch -- "$action" "$@" ;;
esac
