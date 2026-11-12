"""Run the actual pinned SpecTec Module_ok relation on canonical module JSONL.

python3 -m experiments.wasm.check MODULES.jsonl prints one verdict per module,
exits 1 for invalid modules, and raises an explicit error for malformed inputs or
execution failures. This is finite execution evidence, not an ITP certificate.
"""
from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys

from experiments.wasm.build_oracle import digest, specification_identity
from scripts.toolchain import PROJECT


def check_modules(path: Path) -> list[bool]:
    build: Path = PROJECT / 'build/wasm'
    manifest: object = json.loads((build / 'oracle.json').read_text())
    if not isinstance(manifest, dict):
        raise ValueError('Invalid build/wasm/oracle.json: expected object')
    for field, actual in (
        ('oracle_source_sha256', digest(PROJECT / 'experiments/wasm/oracle.ml')),
        ('oracle_binary_sha256', digest(build / 'oracle.exe')),
        ('specification', specification_identity()),
    ):
        if manifest.get(field) != actual:
            raise ValueError(f'Stale oracle {field}; rerun experiments.wasm.build_oracle')
    source: str = path.read_text()
    count: int = len(source.splitlines())
    if count == 0:
        raise ValueError(f'No modules in {path}')
    result: subprocess.CompletedProcess[str] = subprocess.run(
        [str(build / 'oracle.exe'), str(PROJECT / 'specifications/wasm/spec')],
        input=source, capture_output=True, text=True, check=False, timeout=120,
    )
    if result.returncode != 0:
        raise ChildProcessError(
            f'Module_ok oracle failed for {path}, exit={result.returncode}: '
            f'stdout={result.stdout!r}, stderr={result.stderr!r}'
        )
    lines: list[str] = result.stdout.splitlines()
    if len(lines) != count:
        raise ValueError(f'Oracle returned {len(lines)} verdicts for {count} modules: {result.stdout!r}')
    verdicts: list[bool] = []
    for index, line in enumerate(lines):
        record: object = json.loads(line)
        if not isinstance(record, dict) or record.get('index') != index or type(record.get('module_ok')) is not bool:
            raise ValueError(f'Malformed oracle verdict {index}: {line}')
        verdicts.append(record['module_ok'])
        print(line)
    return verdicts


def main() -> None:
    if len(sys.argv) != 2:
        raise ValueError('Usage: python3 -m experiments.wasm.check MODULES.jsonl')
    verdicts: list[bool] = check_modules(Path(sys.argv[1]))
    raise SystemExit(0 if all(verdicts) else 1)


if __name__ == '__main__':
    main()
