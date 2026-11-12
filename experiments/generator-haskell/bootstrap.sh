#!/usr/bin/env bash
# Bootstrap only this isolated experiment; pass an existing Rocq 9.0.0 bin path.
set -euo pipefail
rocq_bin=${1:?Usage: bootstrap.sh ROCQ_BIN_DIRECTORY}
project=$(git rev-parse --show-toplevel)
cd "$project"
experiment=experiments/generator-haskell
build="$project/build/generator-haskell"
mkdir -p "$build"
rm -f "$build/ready.json"
exec > >(tee "$build/bootstrap.log") 2>&1
python3 - "$experiment/toolchain.toml" "$build" <<'PY'
from hashlib import file_digest
from pathlib import Path
import subprocess
import sys
import tomllib

def archive_config(document: object, section: str) -> tuple[str, str]:
    if not isinstance(document, dict) or not isinstance(document.get(section), dict):
        raise ValueError(f"toolchain.toml requires the {section} table")
    config = document[section]
    if not isinstance(config.get("url"), str) or not isinstance(config.get("sha256"), str):
        raise ValueError(f"toolchain.toml {section} requires string url and sha256")
    return config["url"], config["sha256"]


def digest(path: Path) -> str:
    with path.open("rb") as handle:
        return file_digest(handle, "sha256").hexdigest()


manifest: object = tomllib.loads(Path(sys.argv[1]).read_text())
directory: Path = Path(sys.argv[2])
for section, filename in (("translator", "hs-to-rocq.tar.gz"),
                          ("stack", "stack-ranged.tar.gz"),
                          ("ghc", "ghc-official.tar.xz"),
                          ("indents", "indents-0.5.0.1.tar.gz"),
                          ("indents_cabal", "indents.cabal")):
    url, expected = archive_config(manifest, section)
    archive = directory / filename
    if not archive.exists():
        partial = archive.with_name(archive.name + ".part")
        subprocess.run(["curl", "--fail", "--location", "--retry", "3",
                        "--show-error", "--continue-at", "-", url,
                        "-o", str(partial)], check=True)
        actual = digest(partial)
        if actual != expected:
            raise ValueError(f"{partial}: SHA256 {actual}; expected {expected}")
        partial.replace(archive)
    actual = digest(archive)
    if actual != expected:
        raise ValueError(f"{archive}: SHA256 {actual}; expected {expected}")
PY
source="$build/hs-to-rocq-5e6a7bddfa02b818a9e8490ed107b11bd52a84e4"
if [[ ! -d "$source" ]]; then tar -xzf "$build/hs-to-rocq.tar.gz" -C "$build"; fi
if [[ ! -d "$build/indents-0.5.0.1" ]]; then
  tar -xzf "$build/indents-0.5.0.1.tar.gz" -C "$build"
fi
cp "$build/indents.cabal" "$build/indents-0.5.0.1/indents.cabal"
python3 - "$build" <<'PY'
from hashlib import file_digest, sha256
from pathlib import Path
import sys
import tarfile


def verify_sources(directory: Path, archive_name: str, revisions: dict[str, str]) -> None:
    """Reject changed pinned source files, allowing generated build artifacts."""
    with tarfile.open(directory / archive_name, "r|gz") as archive:
        for member in archive:
            if member.isfile():
                path: Path = directory / member.name
                content = archive.extractfile(member)
                if content is None:
                    raise ValueError(f"Missing archive content: {archive_name}:{member.name}")
                expected: str = sha256(content.read()).hexdigest()
                if member.name in revisions:
                    expected = revisions[member.name]
                with path.open("rb") as installed:
                    actual: str = file_digest(installed, "sha256").hexdigest()
                if actual != expected:
                    raise ValueError(f"Pinned source changed: {path}: SHA256 {actual}; expected {expected}")


directory: Path = Path(sys.argv[1])
verify_sources(directory, "hs-to-rocq.tar.gz", {})
verify_sources(directory, "indents-0.5.0.1.tar.gz", {
    "indents-0.5.0.1/indents.cabal": sha256((directory / "indents.cabal").read_bytes()).hexdigest(),
})
PY
if [[ ! -x "$build/stack" ]]; then
  tar -xzf "$build/stack-ranged.tar.gz" -C "$build"
  install -m 755 "$build/stack-3.11.1-linux-x86_64/stack" "$build/stack"
fi
compiler="$build/ghc-9.10.3-x86_64-unknown-linux"
if [[ ! -x "$compiler/bin/ghc" ]]; then
  tar -xJf "$build/ghc-official.tar.xz" -C "$build"
fi
if [[ ! -f "$compiler/lib/settings" ]]; then
  (
    cd "$compiler"
    ./configure --prefix="$compiler"
    make lib/settings
  )
fi
export PATH="$compiler/bin:$rocq_bin:$PATH"
export STACK_ROOT="$build/stack-root"
mkdir -p "$build/project-stack-work"
if [[ ! -e "$experiment/.stack-work" && ! -L "$experiment/.stack-work" ]]; then
  ln -s ../../build/generator-haskell/project-stack-work "$experiment/.stack-work"
fi
test "$(ghc --numeric-version)" = 9.10.3
rocq --version | head -n 1 | rg -F 'version 9.0.0'
"$build/stack" --stack-yaml "$project/$experiment/stack.yaml" --system-ghc --no-install-ghc \
  --local-bin-path "$build/bin" --jobs 2 build --copy-bins
(
  cd "$source/examples/rocq9.0/base"
  coq_makefile -f _CoqProject -o Makefile
  make -j4
)
python3 - "$build" "$rocq_bin" <<'PY'
import json
from pathlib import Path
import subprocess
import sys

directory: Path = Path(sys.argv[1])
rocq_directory: Path = Path(sys.argv[2]).resolve()
versions: dict[str, str] = {
    "ghc": subprocess.check_output([str(directory / "ghc-9.10.3-x86_64-unknown-linux/bin/ghc"), "--numeric-version"], text=True).strip(),
    "stack": subprocess.check_output([str(directory / "stack"), "--numeric-version"], text=True).strip(),
    "rocq": subprocess.check_output([str(rocq_directory / "rocq"), "--version"], text=True).strip(),
    "rocq_bin": str(rocq_directory),
    "translator_revision": "5e6a7bddfa02b818a9e8490ed107b11bd52a84e4",
}
(directory / "ready.json").write_text(json.dumps(versions, indent=2) + "\n")
PY
