"""Translate the Rust core with pinned Charon/Aeneas, then compile its Lean runner.

Run from the repository root with
``python3 -m experiments.generator-rust.translate`` after bootstrap.
Generated LLBC, Lean modules, manifests, and compiler logs stay under build/.
The handwritten Lean runner only parses arguments and serializes the generated AST.
"""
from __future__ import annotations

import os
import json
import re
from pathlib import Path
import shutil
import subprocess
import time

from scripts.toolchain import PROJECT

EXPERIMENT: Path = PROJECT / 'experiments/generator-rust'
BUILD: Path = PROJECT / 'build/generator-rust'
TOOLS: Path = BUILD / 'tools/aeneas'
RUST_BIN: Path = BUILD / 'rustup/toolchains/nightly-2026-09-17-x86_64-unknown-linux-gnu/bin'


def run(command: list[str], directory: Path, environment: dict[str, str], log: Path) -> None:
    """Save complete external-tool output and fail with the command and log path."""
    print('Running:', ' '.join(command), flush=True)
    started: float = time.monotonic()
    with log.open('w') as output:
        result: subprocess.CompletedProcess[str] = subprocess.run(
            command, cwd=directory, env=environment, text=True,
            stdout=output, stderr=subprocess.STDOUT, check=False, timeout=600,
        )
    print(json.dumps({'event': 'tool_finished', 'command': command[0],
                      'seconds': round(time.monotonic() - started, 3),
                      'exit_code': result.returncode}), flush=True)
    if result.returncode != 0:
        raise ChildProcessError(
            f'Command {command!r} exited {result.returncode}; log={log}\n{log.read_text()}'
        )


def lean_environment(lean_bin: Path, directory: Path, environment: dict[str, str]) -> dict[str, str]:
    """Capture Lake's import/library paths once; direct Lean calls use this same directory."""
    names: tuple[str, ...] = ('LEAN_PATH', 'LEAN_SRC_PATH', 'LD_LIBRARY_PATH', 'LEAN_SYSROOT')
    result: subprocess.CompletedProcess[str] = subprocess.run(
        [str(lean_bin / 'lake'), 'env', 'printenv', '-0', *names],
        cwd=directory, env=environment, text=True, capture_output=True, check=True, timeout=180,
    )
    values: list[str] = result.stdout.split('\0')
    if len(values) != len(names) + 1 or values[-1] != '':
        raise ValueError(f'Lake returned malformed compiler paths: {result.stdout!r}')
    paths: dict[str, str] = dict(zip(names, values[:-1], strict=True))
    (BUILD / 'lean-environment.json').write_text(json.dumps(paths, indent=2) + '\n')
    return environment | paths


def executable_source(path: Path) -> bytes:
    """Reject opaque or unfinished emitted declarations before calling them executable."""
    source: bytes = path.read_bytes()
    if re.search(rb'\b(?:axiom|sorry|admit|noncomputable)\b', source):
        raise ValueError(f'Generated Rust core {path} contains an axiom, unfinished code, or noncomputable declaration')
    return source


def main() -> None:
    """Use actual translated definitions without external generator models or patches."""
    for required in (TOOLS / 'charon', TOOLS / 'aeneas', RUST_BIN / 'rustc'):
        if not required.is_file():
            raise FileNotFoundError(f'Missing pinned tool {required}; run the experiment bootstrap first')
    logs: Path = BUILD / 'logs'
    logs.mkdir(parents=True, exist_ok=True)
    llbc: Path = BUILD / 'llbc'
    llbc.mkdir(exist_ok=True)
    lean: Path = BUILD / 'lean'
    lean.mkdir(exist_ok=True)
    ready: object = json.loads((BUILD / 'bootstrap.json').read_text())
    if not isinstance(ready, dict) or not isinstance(ready.get('lean_bin'), str):
        raise ValueError('bootstrap.json must contain lean_bin; rerun bootstrap with exact Lean 4.31.0')
    lean_bin: Path = Path(ready['lean_bin'])
    environment: dict[str, str] = dict(os.environ)
    environment.update({
        'PATH': str(lean_bin) + os.pathsep + str(RUST_BIN) + os.pathsep + environment['PATH'],
        'RUSTUP_HOME': str(BUILD / 'rustup'),
        'CARGO_HOME': str(BUILD / 'cargo'),
        'CARGO_TARGET_DIR': str(BUILD / 'charon-target'),
        'CHARON_TOOLCHAIN_IS_IN_PATH': '1',
        'RUSTC': str(RUST_BIN / 'rustc'),
        'LD_LIBRARY_PATH': str(RUST_BIN.parent / 'lib'),
        'MATHLIB_CACHE_DIR': str(BUILD / 'mathlib-cache'),
        'MATHLIB_NO_CACHE_ON_UPDATE': '1',
        'LEAN_NUM_THREADS': '1',
    })
    run([str(TOOLS / 'charon'), 'cargo', '--preset=aeneas', '--sysroot', 'default',
         '--dest-file', str(llbc / 'generator_rust.llbc'), '--', '--lib', '--offline'], EXPERIMENT, environment,
        logs / 'charon.log')
    run([str(TOOLS / 'aeneas'), '-backend', 'lean', '-dest', str(lean),
         '-abort-on-error', '-warnings-as-errors', '-no-progress-bar', '-all-computable',
         str(llbc / 'generator_rust.llbc')], EXPERIMENT, environment, logs / 'aeneas.log')
    executable_source(lean / 'GeneratorRust.lean')
    for source in (EXPERIMENT / 'lean').iterdir():
        if source.is_file():
            shutil.copyfile(source, lean / source.name)
    # Resolve the project manifest once; later translations reuse the installed dependencies.
    if not (lean / 'lake-manifest.json').is_file():
        run([str(lean_bin / 'lake'), 'update'], lean, environment, logs / 'lake-update.log')
    compiler_environment: dict[str, str] = lean_environment(lean_bin, lean, environment)
    compiled: Path = lean / '.lake/build/lib/lean'
    compiled.mkdir(parents=True, exist_ok=True)
    for module in ('GeneratorRust', 'Main', 'WasmMain'):
        run([str(lean_bin / 'lean'), '-j', '1', '-M', '3100',
             '-o', str(compiled / (module + '.olean')), module + '.lean'],
            lean, compiler_environment, logs / (module + '.log'))
    print(f'Translated and compiled: {lean}', flush=True)


if __name__ == '__main__':
    main()
