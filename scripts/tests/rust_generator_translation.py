"""Execute original Rust, extracted Rust, and actual Aeneas Lean on common fixtures.

Run ``python3 -m scripts.tests.rust_generator_translation`` after the experiment's
bootstrap and translate commands. This is explicit experimental integration work,
not a default production test or a proof of generator properties/equivalence.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
from typing import NamedTuple, cast

from scripts.tests.generator_contract import fold_digest, inspect_record
from scripts.toolchain import PROJECT


class Case(NamedTuple):
    count: int
    nodes: int
    seed: int


BUILD: Path = PROJECT / 'build/generator-rust'
SOURCE: Path = PROJECT / 'experiments/generator-rust'


def output_lines(command: list[str], environment: dict[str, str]) -> list[str]:
    """Execute the real program and reject failures before decoding its output."""
    result: subprocess.CompletedProcess[str] = subprocess.run(
        command, cwd=BUILD / 'lean', env=environment,
        capture_output=True, text=True, check=False, timeout=600,
    )
    if result.returncode != 0:
        raise ChildProcessError(f'{command!r} exited {result.returncode}; stdout={result.stdout!r}; stderr={result.stderr!r}')
    return result.stdout.splitlines()


def parse_records(lines: list[str], case: Case) -> tuple[dict[str, object], ...]:
    """Validate every emitted tree independently, including its type, scope, and exact size."""
    if len(lines) != case.count:
        raise AssertionError(f'{case}: expected {case.count} records; got {len(lines)}')
    output: list[dict[str, object]] = []
    for index, line in enumerate(lines):
        value: object = json.loads(line)
        inspect_record(value, index, case.nodes)
        output.append(cast(dict[str, object], value))
    return tuple(output)


def records(executable: Path, case: Case, environment: dict[str, str]) -> tuple[dict[str, object], ...]:
    """Run a native CLI with one deterministic fixture."""
    command: list[str] = [str(executable), str(case.count), str(case.nodes), str(case.seed)]
    return parse_records(output_lines(command, environment), case)


def translated_records(lean_bin: Path, cases: tuple[Case, ...], environment: dict[str, str]) -> tuple[tuple[dict[str, object], ...], ...]:
    """Call the compiled Lean CLI for all fixtures in one interpreter process."""
    batch: Path = BUILD / 'lean/RunCases.lean'
    calls: list[str] = [
        '  main ' + json.dumps([str(case.count), str(case.nodes), str(case.seed)])
        for case in cases
    ]
    batch.write_text('import Main\n\n#eval do\n' + '\n'.join(calls) + '\n')
    expected: int = sum(case.count for case in cases)
    print(json.dumps({'event': 'execute_lean_batch', 'cases': len(cases), 'samples': expected}), flush=True)
    lines: list[str] = output_lines([str(lean_bin / 'lean'), str(batch)], environment)
    if len(lines) != expected:
        raise AssertionError(f'Lean batch: expected {expected} records; got {len(lines)}')
    groups: list[tuple[dict[str, object], ...]] = []
    offset: int = 0
    for case in cases:
        groups.append(parse_records(lines[offset:offset + case.count], case))
        offset += case.count
    return tuple(groups)


def build_native() -> tuple[Path, Path]:
    """Build preserved and extracted sources using the exact Charon Rust compiler."""
    rust_bin: Path = BUILD / 'rustup/toolchains/nightly-2026-09-17-x86_64-unknown-linux-gnu/bin'
    environment: dict[str, str] = dict(os.environ)
    environment.update({'RUSTC': str(rust_bin / 'rustc'), 'CARGO_HOME': str(BUILD / 'cargo')})
    executables: list[Path] = []
    for name, manifest, binary in (
        ('original-target', SOURCE / 'original/Cargo.toml', 'sample'),
        ('native-target', SOURCE / 'native/Cargo.toml', 'generator-rust-native'),
    ):
        target: Path = BUILD / name
        subprocess.run(
            [str(rust_bin / 'cargo'), 'build', '--manifest-path', str(manifest),
             '--target-dir', str(target), '--release', '--locked', '--offline'],
            env=environment, check=True,
        )
        executables.append(target / 'release' / binary)
    return executables[0], executables[1]


def main() -> None:
    """Compare complete trees and RNG state, including modulo-2^64 edge seeds."""
    original, native = build_native()
    ready: object = json.loads((BUILD / 'bootstrap.json').read_text())
    if not isinstance(ready, dict) or not isinstance(ready.get('lean_bin'), str):
        raise ValueError('bootstrap.json must contain the exact lean_bin path')
    lean_bin: Path = Path(ready['lean_bin'])
    paths: object = json.loads((BUILD / 'lean-environment.json').read_text())
    names: tuple[str, ...] = ('LEAN_PATH', 'LEAN_SRC_PATH', 'LD_LIBRARY_PATH', 'LEAN_SYSROOT')
    if not isinstance(paths, dict) or any(not isinstance(paths.get(name), str) for name in names):
        raise ValueError('lean-environment.json must contain Lake compiler paths; rerun translation')
    environment: dict[str, str] = dict(os.environ)
    environment.update({name: paths[name] for name in names})
    environment['LEAN_NUM_THREADS'] = '1'
    cases: tuple[Case, ...] = tuple(
        Case(8, nodes, seed)
        for nodes in (1, 2, 3, 4, 16, 64, 256, 1024)
        for seed in (17, 2026, 9001)
    ) + (Case(1, 64, (1 << 64) - 1),)
    translated: tuple[tuple[dict[str, object], ...], ...] = translated_records(lean_bin, cases, environment)
    results: list[dict[str, int]] = []
    for case, lean in zip(cases, translated, strict=True):
        preserved: tuple[dict[str, object], ...] = records(original, case, environment)
        extracted: tuple[dict[str, object], ...] = records(native, case, environment)
        digests: list[int] = []
        for index, (old, rust, generated) in enumerate(zip(preserved, extracted, lean, strict=True)):
            for field in ('index', 'type', 'expr'):
                if old[field] != rust[field] or rust[field] != generated[field]:
                    raise AssertionError(f'{case}, sample={index}: {field} differs across original Rust, core Rust, and generated Lean')
            if (type(rust.get('state')) is not int or type(generated.get('state')) is not int
                    or rust['state'] != generated['state']):
                raise AssertionError(f'{case}, sample={index}: final RNG state differs or is missing')
            checked = inspect_record(generated, index, case.nodes)
            if checked.digest != rust['digest']:
                raise AssertionError(f'{case}, sample={index}: original digest disagrees with independent AST traversal')
            digests.append(checked.digest)
        checksum: int = fold_digest(tuple(digests))
        results.append({'count': case.count, 'nodes': case.nodes, 'seed': case.seed, 'checksum': checksum})
        print(f'Passed count={case.count} nodes={case.nodes} seed={case.seed} checksum={checksum}', flush=True)
    evidence: Path = BUILD / 'comparison.json'
    evidence.write_text(json.dumps({
        'cases': results, 'samples': sum(case.count for case in cases),
        'execution': 'Lean #eval batch calling main from the compiled Main module',
    }, indent=2) + '\n')
    print(f'Compared {sum(case.count for case in cases)} complete ASTs and final RNG states; evidence={evidence}')


if __name__ == '__main__':
    main()
