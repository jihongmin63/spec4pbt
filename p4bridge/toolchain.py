"""Build the vendored Lean translator against the pinned official P4-SpecTec."""
import argparse
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile

PROJECT = Path(__file__).resolve().parents[1]
SUBMODULE = 'external/p4-spectec'
UPSTREAM = 'https://github.com/kaist-plrg/p4-spectec.git'
BACKEND_ORIGIN_REVISION = 'd150aa6e53e3f572bc4b02299c05d6d6cee9d6c0'
BUILD_DIRECTORY = 'translator/_build'
TRANSLATOR_TARGET = 'p4spec/lib/lean-skeleton/main.exe'
METADATA_TARGET = 'p4spec/lib/spec4pbt-metadata/metadata.exe'
EXECUTABLE = '_build/default/' + TRANSLATOR_TARGET
METADATA_EXECUTABLE = '_build/default/' + METADATA_TARGET


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


def check_checkout(root, revision, *, label='Official submodule'):
    root = Path(root).resolve()
    if not root.is_dir():
        raise ValueError(f'{label} checkout missing: {root}; run scripts/bootstrap-p4-spectec')
    actual_root = Path(command(['git', 'rev-parse', '--show-toplevel'], root)).resolve()
    if actual_root != root:
        raise ValueError(f'Expected a {label.lower()} checkout root, received {root}')
    actual = command(['git', 'rev-parse', 'HEAD'], root)
    if actual != revision:
        raise ValueError(f'{label} revision mismatch: expected {revision}, got {actual}: {root}')
    if command(['git', 'status', '--porcelain', '--untracked-files=no'], root):
        raise ValueError(f'{label} has dirty tracked files: {root}; keep integration outside upstream')
    return root


def _source_identity(project):
    revision = pinned_revision(project)
    check_checkout(project / SUBMODULE, revision)
    sources = project / 'translator/src'
    patches = project / 'translator/patches'
    for required in [sources / 'main.ml', sources / 'dune', patches / 'algo-defs.patch']:
        if not required.is_file():
            raise ValueError(f'Vendored translator source missing: {required}')
    files = [project / 'p4bridge/metadata.ml', project / 'p4bridge/toolchain.py']
    for directory in [sources, patches]:
        files.extend(path for path in sorted(directory.rglob('*')) if path.is_file())
    hashes = {path.relative_to(project).as_posix(): digest(path) for path in sorted(files)}
    return {'upstream_url': UPSTREAM, 'upstream_revision': revision,
            'backend_origin_revision': BACKEND_ORIGIN_REVISION,
            'sources_sha256': hashlib.sha256(
                json.dumps(hashes, sort_keys=True, separators=(',', ':')).encode()).hexdigest()}


def _binary_identity(root):
    paths = {'translator_sha256': root / EXECUTABLE,
             'metadata_executable_sha256': root / METADATA_EXECUTABLE}
    for path in paths.values():
        if not path.is_file() or not os.access(path, os.X_OK):
            raise ValueError(f'Local translator build is unavailable: {path}; run scripts/build-translator')
    return {name: digest(path) for name, path in paths.items()}


def _checked_identity(project, switch=None):
    stamp = project / BUILD_DIRECTORY / 'toolchain.json'
    try:
        recorded = json.loads(stamp.read_text())
    except (OSError, ValueError) as error:
        raise ValueError('Local translator build is unavailable; run scripts/build-translator') from error
    if not isinstance(recorded, dict) or not isinstance(recorded.get('switch'), str):
        raise ValueError('Local translator build is invalid; run scripts/build-translator')
    chosen_switch = recorded['switch'] if switch is None else switch
    actual = {**_source_identity(project), 'switch': chosen_switch,
              **_binary_identity(project / BUILD_DIRECTORY / 'p4-spectec')}
    if actual != recorded:
        raise ValueError('Local translator build is stale or uses a different switch; run scripts/build-translator')
    return actual


@dataclass(frozen=True)
class Toolchain:
    project: Path
    root: Path
    revision: str
    executable: Path
    helper: Path
    switch: str

    def identity(self):
        return _checked_identity(self.project, self.switch)


def resolve_toolchain(project=PROJECT, switch=None):
    project = Path(project).resolve()
    identity = _checked_identity(project, switch)
    root = project / BUILD_DIRECTORY / 'p4-spectec'
    return Toolchain(project, root, identity['upstream_revision'], root / EXECUTABLE,
                     root / METADATA_EXECUTABLE, identity['switch'])


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



def build(project=PROJECT, switch=None):
    project = Path(project).resolve()
    directory = project / BUILD_DIRECTORY
    directory.mkdir(parents=True, exist_ok=True)
    stamp = directory / 'toolchain.json'
    # A failed or interrupted rebuild must not retain an earlier success stamp.
    stamp.unlink(missing_ok=True)
    before = _source_identity(project)
    chosen_switch = switch if switch is not None else command(['opam', 'switch', 'show'], project)
    if not chosen_switch:
        raise ValueError('No active opam switch; select one with --switch')
    root = directory / 'p4-spectec'
    if root.is_symlink():
        root.unlink()
    elif root.exists():
        shutil.rmtree(root)
    root.mkdir()
    archive = directory / 'upstream.tar'
    try:
        command(['git', 'archive', '--format=tar', '--output=' + str(archive),
                 before['upstream_revision']], project / SUBMODULE)
        with tarfile.open(archive) as source:
            source.extractall(root, filter='data')
    finally:
        archive.unlink(missing_ok=True)
    # Stop Git discovery before it reaches the surrounding project. git apply
    # then edits only this disposable archive, without a repository or index.
    patch_environment = os.environ.copy()
    for key in ['GIT_DIR', 'GIT_WORK_TREE', 'GIT_INDEX_FILE']:
        patch_environment.pop(key, None)
    patch_environment['GIT_CEILING_DIRECTORIES'] = str(directory)
    for patch in sorted((project / 'translator/patches').glob('*.patch')):
        command(['git', 'apply', '--check', patch], root, env=patch_environment)
        command(['git', 'apply', patch], root, env=patch_environment)
    shutil.copytree(project / 'translator/src', root / 'p4spec/lib/lean-skeleton')
    helper_source = root / 'p4spec/lib/spec4pbt-metadata'
    helper_source.mkdir()
    shutil.copyfile(project / 'p4bridge/metadata.ml', helper_source / 'metadata.ml')
    (helper_source / 'dune').write_text(
        '(executable\n (name metadata)\n (libraries pass yojson))\n')
    command(['opam', 'exec', '--switch=' + chosen_switch, '--', 'dune', 'build',
             '--root', root, TRANSLATOR_TARGET, METADATA_TARGET], root, timeout=1800)
    if before != _source_identity(project):
        raise ValueError('Translator inputs changed during build; run scripts/build-translator again')
    identity = {**before, 'switch': chosen_switch, **_binary_identity(root)}
    temporary_stamp = stamp.with_suffix('.json.tmp')
    temporary_stamp.write_text(json.dumps(identity, indent=2) + '\n')
    temporary_stamp.replace(stamp)
    return resolve_toolchain(project, chosen_switch)


def metadata_executable(project, tool):
    if Path(project).resolve() != tool.project:
        raise ValueError('Metadata helper belongs to another project; run scripts/build-translator')
    tool.identity()
    return tool.helper


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['bootstrap', 'build', 'check'])
    parser.add_argument('--project', type=Path, default=PROJECT)
    parser.add_argument('--source', type=Path)
    parser.add_argument('--switch', help='opam switch (build defaults to the active switch)')
    args = parser.parse_args()
    if args.action == 'bootstrap':
        print(bootstrap(args.project, args.source))
    else:
        tool = (build if args.action == 'build' else resolve_toolchain)(args.project, args.switch)
        if args.action == 'check':
            metadata_executable(args.project, tool)
        print(json.dumps(tool.identity(), indent=2))


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
