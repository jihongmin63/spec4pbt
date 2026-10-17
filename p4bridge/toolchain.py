"""Keep the official specification and the Docker Lean translator independently pinned."""
import argparse
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

PROJECT = Path(__file__).resolve().parents[1]
SUBMODULE = 'external/p4-spectec'
UPSTREAM = 'https://github.com/kaist-plrg/p4-spectec.git'
DONOR_REVISION = 'd150aa6e53e3f572bc4b02299c05d6d6cee9d6c0'
EXECUTABLE = '_build/default/p4spec/lib/lean-skeleton/main.exe'


def command(args, cwd, *, env=None, timeout=300):
    result = subprocess.run([str(arg) for arg in args], cwd=cwd, env=env,
                            text=True, capture_output=True, timeout=timeout)
    if result.returncode:
        raise ValueError(f"Command failed ({result.returncode}): {args!r}\n{result.stdout}\n{result.stderr}")
    return result.stdout.strip()


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def pinned_revision(project):
    entry = command(['git', 'ls-files', '--stage', '--', SUBMODULE], project).split()
    if len(entry) != 4 or entry[0] != '160000':
        raise ValueError(f'{SUBMODULE} must be a pinned Git submodule')
    return entry[1]


def check_checkout(root, revision, *, label='Donor'):
    root = Path(root).resolve()
    if not root.is_dir():
        raise ValueError(f'{label} checkout missing: {root}')
    actual_root = Path(command(['git', 'rev-parse', '--show-toplevel'], root)).resolve()
    if actual_root != root:
        raise ValueError(f'Expected a {label.lower()} checkout root, received {root}')
    actual = command(['git', 'rev-parse', 'HEAD'], root)
    if actual != revision:
        raise ValueError(f'{label} revision mismatch: expected {revision}, got {actual}: {root}')
    if command(['git', 'status', '--porcelain', '--untracked-files=no'], root):
        raise ValueError(f'{label} has dirty tracked files: {root}; keep integration outside upstream')
    return root


@dataclass(frozen=True)
class Toolchain:
    root: Path
    revision: str
    executable: Path
    libraries: Path
    switch: str

    def environment(self):
        env = os.environ.copy()
        # Restrict lookup to this checkout's package, then ordinary switch libraries.
        env['OCAMLPATH'] = str(self.libraries)
        return env

    def identity(self):
        check_checkout(self.root, self.revision)
        return {'revision': self.revision, 'donor_root': str(self.root),
                'translator_sha256': digest(self.executable), 'switch': self.switch}


def resolve_toolchain(project=PROJECT, donor_root=None, switch='spectecx', *, require_built=True):
    # The official specification submodule does not contain the Docker Lean backend.
    revision = DONOR_REVISION
    selected = donor_root or os.environ.get('P4_SPECTEC_ROOT') or '/home/p4-spectec'
    root = check_checkout(selected, revision)
    tool = Toolchain(root, revision, root / EXECUTABLE,
                     root / '_build/install/default/lib', switch)
    if require_built and (not tool.executable.is_file() or not os.access(tool.executable, os.X_OK)
                          or not tool.libraries.is_dir()):
        raise ValueError(f'Donor build missing at {root}; provide the existing dev Docker translator '
                         f'at revision {revision} with --donor-root or P4_SPECTEC_ROOT. '
                         'The official specification submodule has no Lean backend.')
    return tool


def bootstrap(project=PROJECT, source=None):
    project = Path(project).resolve()
    revision = pinned_revision(project)
    destination = project / SUBMODULE
    if (destination / '.git').exists():
        check_checkout(destination, revision, label='Official submodule')
        command(['git', 'submodule', 'init', '--', SUBMODULE], project)
        command(['git', 'submodule', 'sync', '--', SUBMODULE], project)
        return destination
    if source is not None:
        source = Path(source).resolve()
        # Local source can have another HEAD, but it must contain the exact commit.
        command(['git', 'cat-file', '-e', revision + '^{commit}'], source)
        command(['git', 'clone', '--no-hardlinks', '--no-checkout', source, destination], project)
        command(['git', 'checkout', '--detach', revision], destination)
        command(['git', 'remote', 'set-url', 'origin', UPSTREAM], destination)
        command(['git', 'submodule', 'init', '--', SUBMODULE], project)
        command(['git', 'submodule', 'sync', '--', SUBMODULE], project)
        command(['git', 'submodule', 'absorbgitdirs', '--', SUBMODULE], project)
    else:
        try:
            command(['git', 'submodule', 'sync', '--', SUBMODULE], project)
            command(['git', 'submodule', 'update', '--init', '--', SUBMODULE], project)
        except ValueError as error:
            raise ValueError(f'{error}\nCould not fetch the official specification at {revision}. '
                             'Check access to its upstream or use --source with a local cache containing that commit.') from error
    check_checkout(destination, revision, label='Official submodule')
    return destination


def build(project=PROJECT, donor_root=None, switch='spectecx'):
    project = Path(project).resolve()
    tool = resolve_toolchain(project, donor_root, switch)
    directory = project / 'p4bridge/_build'
    directory.mkdir(parents=True, exist_ok=True)
    source = project / 'p4bridge/metadata.ml'
    shutil.copyfile(source, directory / 'metadata.ml')
    command(['opam', 'exec', '--switch=' + switch, '--', 'ocamlfind', 'ocamlopt',
             '-linkpkg', '-package', 'p4spectec.pass,yojson', 'metadata.ml', '-o', 'metadata.exe'],
            directory, env=tool.environment())
    identity = {**tool.identity(), 'metadata_source_sha256': digest(source),
                'metadata_executable_sha256': digest(directory / 'metadata.exe')}
    (directory / 'toolchain.json').write_text(json.dumps(identity, indent=2) + '\n')
    return tool


def metadata_executable(project, tool):
    directory = Path(project) / 'p4bridge/_build'
    try:
        recorded = json.loads((directory / 'toolchain.json').read_text())
        actual = {**tool.identity(), 'metadata_source_sha256': digest(Path(project) / 'p4bridge/metadata.ml'),
                  'metadata_executable_sha256': digest(directory / 'metadata.exe')}
    except (OSError, ValueError) as error:
        raise ValueError('Metadata build is unavailable; run scripts/build-translator') from error
    if recorded != actual:
        raise ValueError('Metadata build is stale or uses a different donor; run scripts/build-translator')
    return directory / 'metadata.exe'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['bootstrap', 'build', 'check'])
    parser.add_argument('--project', type=Path, default=PROJECT)
    parser.add_argument('--source', type=Path)
    parser.add_argument('--donor-root', type=Path)
    parser.add_argument('--switch', default='spectecx')
    args = parser.parse_args()
    if args.action == 'bootstrap':
        print(bootstrap(args.project, args.source))
    else:
        tool = (build if args.action == 'build' else resolve_toolchain)(
            args.project, args.donor_root, args.switch)
        if args.action == 'check':
            metadata_executable(args.project, tool)
        print(json.dumps(tool.identity(), indent=2))


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
