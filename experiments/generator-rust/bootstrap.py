"""Provision the pinned Rust-to-Lean experiment without changing global tools.

Run from the repository root:
  PYTHONPATH=. python3 experiments/generator-rust/bootstrap.py RUSTUP LEAN_BIN PACKAGE_CACHE

RUSTUP is an existing rustup executable. LEAN_BIN contains the baseline Lean4.31
tools. PACKAGE_CACHE is a Lake packages directory at the backend's exact locked
revisions. It is copied into this experiment; existing project packages remain
untouched. Installations, archives and a readiness record live under build/.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tomllib
from typing import cast

from scripts.toolchain import PROJECT, check_checkout


BUILD: Path = PROJECT / "build/generator-rust"
CONFIG: Path = PROJECT / "experiments/generator-rust/toolchain.toml"


@dataclass(frozen=True)
class Pins:
    release: str
    url: str
    sha256: str
    source_url: str
    source_sha256: str
    charon_revision: str
    rust_toolchain: str
    rust_version: str
    lean_version: str
    mathlib_revision: str
    cache_modules: tuple[str, ...]


def field(table: object, name: str) -> str:
    if not isinstance(table, dict):
        raise ValueError(f"Toolchain config requires a table for field {name}")
    value: object = table.get(name)
    if not isinstance(value, str) or not value:
        raise ValueError(f"Toolchain config requires nonempty string field {name}")
    return value


def read_pins() -> Pins:
    with CONFIG.open("rb") as stream:
        data: dict[str, object] = tomllib.load(stream)
    if data.get("schema_version") != 1:
        raise ValueError(f"Unsupported toolchain config schema: {CONFIG}")
    aeneas, rust, lean = data.get("aeneas"), data.get("rust"), data.get("lean")
    cache_modules: object = lean.get("cache_modules") if isinstance(lean, dict) else None
    if not isinstance(cache_modules, list) or not cache_modules or not all(
        isinstance(module, str) and module.startswith(("Mathlib.", "Batteries.")) for module in cache_modules
    ):
        raise ValueError("Toolchain config requires nonempty lean.cache_modules module names")
    return Pins(field(aeneas, "release"), field(aeneas, "url"), field(aeneas, "sha256"),
                field(aeneas, "source_url"), field(aeneas, "source_sha256"),
                field(aeneas, "charon_revision"), field(rust, "toolchain"), field(rust, "version"),
                field(lean, "version"), field(lean, "mathlib_revision"),
                tuple(cast(list[str], cache_modules)))


def sha256(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def command(arguments: list[str], environment: dict[str, str]) -> str:
    print(json.dumps({"event": "command", "arguments": arguments}), flush=True)
    result = subprocess.run(arguments, env=environment, cwd=PROJECT, text=True,
                            capture_output=True, check=False)
    if result.stderr:
        sys.stderr.write(result.stderr)
    if result.returncode:
        raise ChildProcessError(f"Command exited {result.returncode}: {arguments!r}\n"
                                f"stdout: {result.stdout}\nstderr: {result.stderr}")
    return result.stdout.strip()


def download(url: str, expected: str, path: Path, environment: dict[str, str]) -> Path:
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        temporary: Path = path.with_suffix(path.suffix + ".part")
        command(["curl", "--fail-with-body", "--location", "--silent", "--show-error",
                 "--retry", "3", "--retry-all-errors", "--output", str(temporary), url], environment)
        actual: str = sha256(temporary)
        if actual != expected:
            raise ValueError(f"Archive SHA256 mismatch for {url}: expected {expected}, got {actual}; "
                             f"retained {temporary}")
        temporary.replace(path)
    actual = sha256(path)
    if actual != expected:
        raise ValueError(f"Cached archive SHA256 mismatch: {path}; expected {expected}, got {actual}")
    return path


def extract_release(archive: Path, destination: Path) -> None:
    if destination.exists():
        return
    destination.mkdir(parents=True)
    with tarfile.open(archive) as stream:
        stream.extractall(destination, filter="data")


def extract_source(archive: Path, destination: Path) -> None:
    if destination.exists():
        return
    temporary: Path = destination.with_name(destination.name + "-unpack")
    temporary.mkdir(parents=True, exist_ok=False)
    with tarfile.open(archive) as stream:
        stream.extractall(temporary, filter="data")
    roots: list[Path] = list(temporary.iterdir())
    if len(roots) != 1 or not roots[0].is_dir():
        raise ValueError(f"Expected one source root in {archive}; retained {temporary}")
    roots[0].replace(destination)
    temporary.rmdir()


def verify_release_files(archive: Path, directory: Path) -> None:
    required: set[str] = {"aeneas", "charon", "charon-driver", "rust-toolchain",
                          "backends/lean/lean-toolchain", "backends/lean/lake-manifest.json",
                          "backends/lean/lakefile.lean"}
    seen: set[str] = set()
    with tarfile.open(archive, mode="r|gz") as stream:
        for member in stream:
            name: str = member.name.removeprefix("./")
            if name not in required and not (
                name.startswith("backends/lean/Aeneas") and name.endswith(".lean")
            ):
                continue
            if not member.isfile():
                raise ValueError(f"Official archive lacks regular file {name}: {archive}")
            seen.add(name)
            contents = stream.extractfile(member)
            if contents is None:
                raise ValueError(f"Cannot read archive member {name}: {archive}")
            with contents:
                expected: str = hashlib.file_digest(contents, "sha256").hexdigest()
            actual: str = sha256(directory / name)
            if actual != expected:
                raise ValueError(f"Installed release differs from archive: {directory/name}; "
                                 f"expected {expected}, got {actual}")
    if not required <= seen:
        raise ValueError(f"Official archive lacks required files {sorted(required - seen)}: {archive}")


def copy_packages(cache: Path, backend: Path) -> None:
    parsed: object = json.loads((backend / "lake-manifest.json").read_text())
    if not isinstance(parsed, dict) or not isinstance(parsed.get("packages"), list):
        raise ValueError(f"Invalid backend dependency manifest: {backend}")
    packages: list[object] = cast(list[object], parsed["packages"])
    target: Path = backend / ".lake/packages"
    target.mkdir(parents=True, exist_ok=True)
    for package in packages:
        name, revision = field(package, "name"), field(package, "rev")
        source: Path = cache / name
        check_checkout(source, revision, label="Lean dependency cache")
        destination: Path = target / name
        if not destination.exists():
            shutil.copytree(source, destination, symlinks=True)
        check_checkout(destination, revision, label="Installed Lean dependency")


def missing_modules(modules: tuple[str, ...], packages: Path) -> list[str]:
    roots: dict[str, str] = {"Mathlib": "mathlib", "Batteries": "batteries"}
    return [module for module in modules
            if not (packages / roots[module.split(".")[0]] / ".lake/build/lib/lean"
                    / (module.replace(".", "/") + ".olean")).exists()]


def main(arguments: list[str]) -> None:
    if len(arguments) != 3:
        raise ValueError("usage: PYTHONPATH=. python3 experiments/generator-rust/bootstrap.py "
                         "RUSTUP LEAN_BIN PACKAGE_CACHE (run from repository root)")
    rustup, lean_bin, cache = tuple(Path(value).resolve() for value in arguments)
    (BUILD / "bootstrap.json").unlink(missing_ok=True)
    pins: Pins = read_pins()
    environment: dict[str, str] = dict(os.environ)
    environment.update({"RUSTUP_HOME": str(BUILD / "rustup"), "CARGO_HOME": str(BUILD / "cargo"),
                        "MATHLIB_NO_CACHE_ON_UPDATE": "1",
                        "PATH": str(lean_bin) + os.pathsep + environment.get("PATH", "")})
    lean: str = command([str(lean_bin / "lean"), "--version"], environment)
    if f"version {pins.lean_version}," not in lean:
        raise ValueError(f"Expected Lean {pins.lean_version} at {lean_bin}, got {lean}")
    release: Path = download(pins.url, pins.sha256, BUILD / "downloads/aeneas-compatible.tar.gz", environment)
    source: Path = download(pins.source_url, pins.source_sha256, BUILD / "downloads/aeneas-source.tar.gz", environment)
    installation: Path = BUILD / "tools/aeneas"
    sources: Path = BUILD / "tools/aeneas-source"
    extract_release(release, installation)
    extract_source(source, sources)
    verify_release_files(release, installation)
    charon_pins: list[str] = [line.strip() for line in (sources / "charon-pin").read_text().splitlines()
                              if line.strip() and not line.lstrip().startswith("#")]
    if charon_pins != [pins.charon_revision]:
        raise ValueError("Aeneas source Charon pin does not match toolchain.toml")
    with (installation / "rust-toolchain").open("rb") as stream:
        rust_configuration: dict[str, object] = tomllib.load(stream)
    if field(rust_configuration.get("toolchain"), "channel") != pins.rust_toolchain:
        raise ValueError("Aeneas release Rust toolchain does not match toolchain.toml")
    mathlib: str = command(["git", "-C", str(cache / "mathlib"), "rev-parse", "HEAD"], environment)
    if mathlib != pins.mathlib_revision:
        raise ValueError(f"Expected mathlib {pins.mathlib_revision}, got {mathlib}")
    copy_packages(cache, installation / "backends/lean")
    required_components: set[str] = {"cargo-x86_64-unknown-linux-gnu",
        "rust-std-x86_64-unknown-linux-gnu", "rustc-x86_64-unknown-linux-gnu",
        "rustc-dev-x86_64-unknown-linux-gnu"}
    components: Path = BUILD / "rustup/toolchains" / (
        pins.rust_toolchain + "-x86_64-unknown-linux-gnu/lib/rustlib/components")
    installed: set[str] = set(components.read_text().splitlines()) if components.exists() else set()
    if not required_components <= installed:
        command([str(rustup), "toolchain", "install", pins.rust_toolchain, "--profile", "minimal",
                 "--component", "rustc-dev", "--no-self-update"], environment)
    backend: Path = installation / "backends/lean"
    packages: Path = backend / ".lake/packages"
    environment["MATHLIB_CACHE_DIR"] = str(BUILD / "mathlib-cache")
    command([str(lean_bin / "lake"), "-d", str(backend), "exe", "cache", "get",
             *pins.cache_modules], environment)
    remaining: list[str] = missing_modules(pins.cache_modules, packages)
    if remaining:
        raise FileNotFoundError(f"Lean dependency cache retrieval left modules missing in {packages}: {remaining}")
    compiler: Path = BUILD / "rustup/toolchains" / (pins.rust_toolchain + "-x86_64-unknown-linux-gnu/bin/rustc")
    rust: str = command([str(compiler), "--version"], environment)
    if rust != pins.rust_version:
        raise ValueError(f"Expected Rust compiler {pins.rust_version!r}, got {rust!r}")
    record: dict[str, object] = {"aeneas_release": pins.release, "aeneas_archive_sha256": pins.sha256,
        "charon_revision": pins.charon_revision, "rust": rust, "lean": lean,
        "lean_bin": str(lean_bin), "rustup": str(rustup),
        "dependency_cache": str(cache), "configuration_sha256": sha256(CONFIG)}
    (BUILD / "bootstrap.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"event": "ready", "record": str(BUILD / "bootstrap.json")}), flush=True)


if __name__ == "__main__":
    main(sys.argv[1:])
