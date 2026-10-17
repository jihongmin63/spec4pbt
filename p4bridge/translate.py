"""Translate with the unchanged donor, then generate and check observation transport."""
import argparse
import ctypes
import errno
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from pbt.lean_tools import require_timeout
from pbt.observations import _name, load_config, validate_manifest, validate_observation
from p4bridge.toolchain import (
    PROJECT, UPSTREAM, command, digest, metadata_executable, pinned_revision, resolve_toolchain,
)


def _source_files(directory, ancestors=frozenset()):
    # Match donor Util.Filesys.collect_files: sorted recursive traversal,
    # following directory symlinks, except directories named "include".
    real = directory.resolve()
    if real in ancestors:
        raise ValueError(f'Specification directory cycle: {directory}')
    for child in sorted(directory.iterdir()):
        if child.is_dir() and child.name != 'include':
            yield from _source_files(child, ancestors | {real})
        elif child.name.endswith('.watsup'):
            yield child


def source_identity(paths):
    result = {}
    for path in paths:
        files = list(_source_files(path)) if path.is_dir() else [path]
        if not files:
            raise ValueError(f'No .watsup source files: {path}')
        for file in files:
            if not file.is_file():
                raise ValueError(f'Specification file missing: {file}')
            # Preserve lexical paths: swapping two symlink targets must change
            # the identity even when the set of resolved source files is equal.
            result[str(file.absolute())] = digest(file)
    return result


def _publish(source, destination):
    """Linux atomic no-replace directory rename (including racing empty dirs)."""
    libc = ctypes.CDLL(None, use_errno=True)
    rename = getattr(libc, 'renameat2', None)
    if rename is None:
        raise OSError('Atomic no-replace directory publication requires renameat2 (Linux)')
    rename.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
    rename.restype = ctypes.c_int
    if rename(-100, os.fsencode(source), -100, os.fsencode(destination), 1) != 0:
        code = ctypes.get_errno()
        if code == errno.EEXIST:
            raise FileExistsError(f'Refusing to overwrite existing output: {destination}')
        raise OSError(code, os.strerror(code), str(destination))


def generate(project, output_dir, config, sources, *, donor_root=None, switch='spectecx',
             executable=False, namespace='P4Observation', timeout_seconds=300,
             transport_model=None):
    project = Path(project).resolve()
    output = Path(output_dir)
    if not output.is_absolute():
        output = project / output
    if os.path.lexists(output):
        raise FileExistsError(f'Refusing to overwrite existing output: {output}')
    output = output.resolve()
    if not output.is_relative_to(project) or output == project:
        raise ValueError('Output directory must be inside the Lean project')
    relative = output.relative_to(project)
    for part in relative.parts:
        _name(part, 'output module path', dotted=False)
    _name(namespace, 'transport namespace')
    timeout = require_timeout(timeout_seconds)
    if not sources:
        raise ValueError('At least one specification path is required')
    sources = [Path(source).resolve() for source in sources]
    config = Path(config).resolve()
    transport_model = Path(transport_model).resolve() if transport_model is not None else None
    configuration = load_config(config)
    tool = resolve_toolchain(PROJECT, donor_root, switch)
    helper = metadata_executable(PROJECT, tool)
    before = {'toolchain': tool.identity(),
              'p4_spectec': {'url': UPSTREAM, 'revision': pinned_revision(PROJECT)},
              'sources': source_identity(sources),
              'config_sha256': digest(config), 'metadata_sha256': digest(helper),
              'lean_toolchain_sha256': digest(project / 'lean-toolchain')}
    if transport_model is not None:
        before['transport_model'] = {'path': str(transport_model), 'sha256': digest(transport_model)}
    spec_module = '.'.join(relative.parts) + '.Spec'
    transport_module = '.'.join(relative.parts) + '.Transport'
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.p4-observation-', dir=output.parent) as directory:
        stage = Path(directory)
        bundle = stage / relative
        bundle.mkdir(parents=True)
        # Capture bytes unchanged. In particular, keep the embedded runtime and namespace.
        args = [str(tool.executable)] + (['--executable'] if executable else []) + [str(p) for p in sources]
        result = subprocess.run(args, cwd=project, capture_output=True, timeout=timeout)
        if result.returncode:
            raise ValueError(f'Donor translation failed ({result.returncode}):\n'
                             + result.stderr.decode('utf-8', errors='replace'))
        (bundle / 'Spec.lean').write_bytes(result.stdout)
        settings = stage / 'config.json'
        settings.write_text(json.dumps(configuration))
        model_args = ['--transport-model', transport_model] if transport_model is not None else []
        payload = json.loads(command([helper, '--spec-module', spec_module, '--namespace', namespace,
                                      '--config', settings, *model_args, *sources], project, timeout=timeout))
        if not isinstance(payload, dict) or set(payload) != {'manifest', 'transport'}:
            raise ValueError('Metadata helper returned an invalid response')
        manifest = validate_manifest(payload['manifest'])
        entries = configuration.get('observations')
        if not isinstance(entries, list) or not entries:
            raise ValueError('Observation config must contain at least one observation')
        for item in entries:
            validate_observation(configuration, item.get('id') if isinstance(item, dict) else None, manifest)
        (bundle / 'Transport.lean').write_text(payload['transport'], encoding='utf-8')
        (bundle / 'manifest.json').write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n')
        shutil.copyfile(config, bundle / 'observations.toml')
        shutil.copyfile(project / 'lean-toolchain', stage / 'lean-toolchain')
        (stage / 'lakefile.toml').write_text('name = "p4_observation_check"\nversion = "0.1.0"\n')
        objects = stage / 'objects'
        (objects / relative).mkdir(parents=True)
        env = os.environ.copy()
        env['LEAN_PATH'] = str(objects)
        for module in ['Spec', 'Transport']:
            command(['lake', 'env', 'lean', '--root', stage, '-o',
                     objects / relative / (module + '.olean'), bundle / (module + '.lean')],
                    stage, env=env, timeout=timeout)
        # Compile each projection too: metadata must resolve to real Lean fields and codecs.
        from pbt.observations import render_view
        for index, item in enumerate(entries):
            selected = validate_observation(configuration, item['id'], manifest)
            view = stage / f'Check{index}.lean'
            view.write_text(render_view(manifest, selected, transport_module, f'P4ViewCheck{index}', '0' * 64))
            command(['lake', 'env', 'lean', '--root', stage, view], stage, env=env, timeout=timeout)
        after = {'toolchain': tool.identity(),
                 'p4_spectec': {'url': UPSTREAM, 'revision': pinned_revision(PROJECT)},
                 'sources': source_identity(sources),
                 'config_sha256': digest(config), 'metadata_sha256': digest(helper),
                 'lean_toolchain_sha256': digest(project / 'lean-toolchain')}
        if transport_model is not None:
            after['transport_model'] = {'path': str(transport_model), 'sha256': digest(transport_model)}
        if before != after:
            raise ValueError('Translation inputs or toolchain changed during generation')
        metadata_executable(PROJECT, tool)
        provenance = {**before, 'schema_version': 1, 'source_paths': [str(p) for p in sources],
                      'mode': 'ordered-executable' if executable else 'ordered',
                      'spec_module': spec_module, 'transport_module': transport_module,
                      'namespace': namespace,
                      'spec_sha256': digest(bundle / 'Spec.lean'),
                      'transport_sha256': digest(bundle / 'Transport.lean'),
                      'manifest_sha256': digest(bundle / 'manifest.json'),
                      'donor_diagnostics': result.stderr.decode('utf-8', errors='replace')}
        (bundle / 'translation.json').write_text(json.dumps(provenance, indent=2, ensure_ascii=False) + '\n')
        _publish(bundle, output)
    return provenance


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=PROJECT)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--config', type=Path, required=True)
    parser.add_argument('--donor-root', type=Path)
    parser.add_argument('--switch', default='spectecx')
    parser.add_argument('--namespace', default='P4Observation')
    parser.add_argument('--transport-model', type=Path,
                        help='Lean declarations choosing external types/instances, inserted inside the transport namespace')
    parser.add_argument('--executable', action='store_true')
    parser.add_argument('--timeout-seconds', type=float, default=300)
    parser.add_argument('specifications', type=Path, nargs='+')
    args = parser.parse_args()
    result = generate(args.project, args.output_dir, args.config, args.specifications,
                      donor_root=args.donor_root, switch=args.switch, executable=args.executable,
                      namespace=args.namespace, timeout_seconds=args.timeout_seconds,
                      transport_model=args.transport_model)
    print(f"Generated and checked {result['transport_module']} in {args.output_dir}")


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, TypeError, subprocess.TimeoutExpired) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
