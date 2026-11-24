"""Build the OCaml bridge in an ignored copy of the pinned frontend."""
from pathlib import Path
import hashlib
import shutil
import subprocess
import fcntl


ROOT = Path(__file__).resolve().parents[2]
STATE = ROOT / '_opam-testing-theorems'
PINNED = STATE / 'sources/p4-spectec'
BRIDGE = ROOT / 'scripts/property/native'


def pinned_source_digest():
    """Identify the unchanged frontend inputs used for the private bridge build."""
    hasher = hashlib.sha256()
    for path in sorted(PINNED.rglob('*.ml')) + [PINNED / 'dune-project']:
        relative = path.relative_to(PINNED)
        hasher.update(str(relative).encode())
        hasher.update(b'\0')
        hasher.update(path.read_bytes())
    return hasher.hexdigest()


def build_bridge():
    parent = STATE / 'build'
    parent.mkdir(parents=True, exist_ok=True)
    with (parent / 'property-bridge.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        return _build_bridge()


def _build_bridge():
    sources = sorted(BRIDGE.glob('*.ml'))
    source_hash = pinned_source_digest()
    digest = hashlib.sha256(b''.join(p.read_bytes() for p in sources) +
                            source_hash.encode()).hexdigest()[:16]
    build = STATE / 'build' / f'property-bridge-{digest}'
    copied = build / 'source'
    executable = copied / '_build/default/p4spec/property_bridge/main.exe'
    if executable.is_file():
        return executable
    build.mkdir(parents=True, exist_ok=True)
    if not copied.exists():
        shutil.copytree(PINNED, copied,
                        ignore=shutil.ignore_patterns('_build', '.git', '_opam'))
    destination = copied / 'p4spec/property_bridge'
    destination.mkdir(parents=True, exist_ok=True)
    for source in sources:
        shutil.copy2(source, destination / source.name)
    (destination / 'dune').write_text(
        '(executable (name main) (libraries p4spectec yojson))\n')
    command = ['bash', str(ROOT / 'environment/env.sh'), 'frontend',
               'dune', 'build', '--root', str(copied), '-j', '2',
               'p4spec/property_bridge/main.exe']
    result = subprocess.run(command, capture_output=True, text=True, timeout=240)
    (build / 'build.log').write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(f'bridge build failed: {build / "build.log"}\n'
                           + (result.stdout + result.stderr)[-5000:])
    (build / 'source-manifest.txt').write_text(
        f'bridge_sha256 {hashlib.sha256(b"".join(p.read_bytes() for p in sources)).hexdigest()}\n'
        f'pinned_source_sha256 {source_hash}\n'
        f'pinned_dune_sha256 {hashlib.sha256((PINNED / "dune-project").read_bytes()).hexdigest()}\n')
    return executable
