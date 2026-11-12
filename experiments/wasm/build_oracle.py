"""Build the isolated Module_ok oracle using an explicitly selected, audited toolchain.

Run from the branch root: python3 -m experiments.wasm.build_oracle DONOR_PROJECT.
The donor must already pass scripts.toolchain.resolve_toolchain's freshness audit
and provide the repository's Wasm native builtin integration. Its existing tool
sources and executables are not modified; only a separate ignored target is added.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

from scripts.toolchain import PROJECT, resolve_toolchain


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def specification_identity() -> dict[str, str]:
    """Reject specification changes relative to the imported upstream checksums."""
    root: Path = PROJECT / 'specifications/wasm'
    expected: dict[str, str] = {}
    for line in (root / 'SHA256SUMS').read_text().splitlines():
        checksum, relative = line.split(maxsplit=1)
        if digest(root / relative) != checksum:
            raise ValueError(f'Wasm source checksum mismatch: {root / relative}')
        expected[relative] = checksum
    return expected


def main() -> None:
    if len(sys.argv) != 2:
        raise ValueError('Usage: python3 -m experiments.wasm.build_oracle DONOR_PROJECT')
    donor: Path = Path(sys.argv[1]).resolve()
    tool = resolve_toolchain(project=donor)
    identity: dict[str, object] = tool.identity()
    source: Path = PROJECT / 'experiments/wasm/oracle.ml'
    checksum: str = digest(source)
    name: str = 'generator-wasm-oracle-' + checksum[:12]
    directory: Path = tool.root / 'p4spec/lib' / name
    directory.mkdir(exist_ok=True)
    shutil.copyfile(source, directory / 'oracle.ml')
    (directory / 'dune').write_text(
        '(executable (name oracle) (modules oracle) '
        '(libraries pass interp_al interface runtime lang domain util diagnostic yojson wasm_builtin_hooks))\n'
    )
    target: str = f'p4spec/lib/{name}/oracle.exe'
    subprocess.run(
        ['opam', 'exec', '--switch=' + tool.switch, '--', 'dune', 'build', '-j', '1',
         '--root', str(tool.root), target], cwd=PROJECT, check=True, timeout=600,
    )
    if tool.identity() != identity:
        raise ValueError(f'Donor toolchain changed during oracle build: {donor}')
    build: Path = PROJECT / 'build/wasm'
    build.mkdir(parents=True, exist_ok=True)
    executable: Path = build / 'oracle.exe'
    shutil.copyfile(tool.root / '_build/default' / target, executable)
    executable.chmod(0o755)
    (build / 'oracle.json').write_text(json.dumps({
        'donor_project': str(donor), 'toolchain': identity,
        'oracle_source_sha256': checksum, 'oracle_binary_sha256': digest(executable),
        'specification': specification_identity(),
    }, indent=2) + '\n')
    print(executable)


if __name__ == '__main__':
    main()
