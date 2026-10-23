"""Dependency worker launched once inside `lake env` (standard library only)."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys


def fingerprint(project, roots, timeout):
    def digest(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def query(flag, source):
        process = subprocess.run(['lean', flag, str(source)], cwd=project,
            capture_output=True, text=True, timeout=timeout, check=True)
        return [Path(line).resolve() for line in process.stdout.splitlines()]

    files = {}
    graph = {}
    for name in ['lakefile.toml', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain']:
        path = project/name
        if path.exists():
            files[str(path)] = digest(path)
    pending = list(roots)
    seen = set()
    while pending:
        path = pending.pop().resolve()
        if path in seen:
            continue
        seen.add(path)
        files[str(path)] = digest(path)
        sources = query('--src-deps', path)
        graph[str(path)] = [str(source) for source in sources]
        pending.extend(source for source in sources if source.is_relative_to(project) and source.exists())
        for artifact in query('--deps', path):
            if not artifact.is_file():
                continue
            files[str(artifact)] = digest(artifact)
            if artifact.is_relative_to(project):
                for suffix in ['.ir', '.olean.private', '.olean.server']:
                    companion = artifact.with_suffix(suffix)
                    if companion.exists():
                        files[str(companion)] = digest(companion)
    return dict(fingerprints=files, graph=graph)


if __name__ == '__main__':
    try:
        print(json.dumps(fingerprint(Path(sys.argv[1]), [Path(p) for p in sys.argv[3:]], float(sys.argv[2]))))
    except subprocess.CalledProcessError as error:
        print(f'Lean dependency query failed: {error.cmd}\n{error.stdout}\n{error.stderr}', file=sys.stderr)
        sys.exit(1)
