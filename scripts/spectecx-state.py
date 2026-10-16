#!/usr/bin/env python3
"""Record/check the installed upstream artifacts against the pinned checkout."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
STAMP = ROOT / ".lake" / "spectecx-install.json"


def output(*command: str) -> str:
    return subprocess.check_output(command, cwd=ROOT, text=True).strip()


def state(switch: str) -> dict[str, str]:
    entry = output("git", "ls-files", "--stage", "--", "external/spectecx").split()
    if len(entry) != 4 or entry[0] != "160000":
        raise ValueError("external/spectecx must be the tracked upstream submodule")
    source = ROOT / "external" / "spectecx"
    actual = output("git", "-C", str(source), "rev-parse", "HEAD")
    if actual != entry[1] or output("git", "-C", str(source), "status", "--porcelain"):
        raise ValueError("SpecTecX checkout differs from the clean pinned submodule")
    prefix = Path(output("opam", "var", f"--switch={switch}", "prefix"))
    library = prefix / "lib" / "spectec"
    files = sorted(path for path in library.rglob("*") if path.is_file())
    if not files:
        raise ValueError("SpecTecX core is not installed; run scripts/bootstrap-spectecx")
    digest = hashlib.sha256()
    for path in files:
        digest.update(str(path.relative_to(library)).encode() + b"\0")
        digest.update(hashlib.sha256(path.read_bytes()).digest())
    return {"revision": actual, "switch": switch, "prefix": str(prefix),
            "library_sha256": digest.hexdigest()}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("record", "check"))
    parser.add_argument("--switch", default="spectecx")
    args = parser.parse_args()
    current = state(args.switch)
    if args.action == "record":
        STAMP.parent.mkdir(parents=True, exist_ok=True)
        STAMP.write_text(json.dumps(current, indent=2) + "\n")
        print(f"Recorded SpecTecX {current['revision']} in {current['prefix']}")
    else:
        if not STAMP.exists() or json.loads(STAMP.read_text()) != current:
            raise ValueError("Installed SpecTecX provenance changed; run scripts/bootstrap-spectecx")
        print(f"Verified SpecTecX {current['revision']}")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error)) from error
