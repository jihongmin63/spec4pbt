#!/usr/bin/env python3
"""Run the pinned AL frontend in a private build copy and preserve evidence.

Inventory, source generation and optional Coq compilation are recorded stages.
Only a complete successful --check run is marked coq_compiled.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
STATE = ROOT / '_opam-testing-theorems'


def owned_path(root, value):
    path = (root / value).resolve()
    if not path.is_relative_to(root.resolve()):
        raise ValueError(f'path outside worktree: {value}')
    return path


def verify_inputs(root, profile):
    entries = profile.get('inputs', [])
    if not entries:
        raise ValueError('profile has no inputs')
    paths, seen = [], set()
    for entry in entries:
        path = owned_path(root, entry['path'])
        if path in seen:
            raise ValueError(f'duplicate input: {entry["path"]}')
        seen.add(path)
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != entry['sha256']:
            raise ValueError(f'SHA-256 mismatch: {entry["path"]}: expected {entry["sha256"]}, got {actual}')
        paths.append(path)
    return paths


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def run_command(command, *, cwd, log, manifest):
    record = {'argv': list(map(str, command)), 'cwd': str(cwd), 'log': str(log)}
    manifest['commands'].append(record)
    with log.open('w') as stream:
        process = subprocess.run(command, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT)
    record['returncode'] = process.returncode
    if process.returncode:
        print(log.read_text()[-6000:], file=sys.stderr)
        raise RuntimeError(f'command failed ({process.returncode}); see {log}')


def prepare_backend(source, run):
    """Never build or patch the archived source directory itself."""
    build_parent = STATE / 'build'
    build_parent.mkdir(parents=True, exist_ok=True)
    build = Path(tempfile.mkdtemp(prefix='al-to-coq-', dir=build_parent))
    target = build / 'source'
    shutil.copytree(source, target, ignore=shutil.ignore_patterns('_build', '.git', '_opam'))
    backend = target / 'p4spec' / 'al_to_coq'
    shutil.copytree(ROOT / 'translator/src', backend)
    # p4spec currently has no explicit dirs filter; root's filter allows p4spec.
    return target, backend


def compile_generated(source, profile, run, manifest):
    """Compile only inside the ignored evidence run; retain every failed run."""
    support = run / 'support'
    shutil.copytree(ROOT / 'translator/coq', support)
    namespace = {'p4': 'P4Spec', 'wasm': 'WasmSpec'}.get(profile, 'FixtureSpec')
    common = [support / 'Execution.v', support / 'Values.v']
    if profile in ['p4', 'wasm']:
        common += [support / 'Builtins/Common.v', support / 'Builtins/P4.v']
    if profile == 'wasm':
        common += [support / f'Builtins/{name}.v' for name in
                   ['WasmScalar', 'WasmFloat', 'WasmVector', 'WasmExecution']]
    generated = source / 'Generated'
    files = common + [generated / name for name in
                      ['Types_0000.v', 'Casts.v', 'References.v', 'Calls.v']]
    files += sorted(generated.glob('Bodies_*.v'))
    files.append(generated / 'Program.v')
    if (generated / 'InductiveRelations.v').is_file():
        files += sorted(generated.glob('InductiveRelations_*.v'))
        files.append(generated / 'InductiveRelations.v')
    files.append(generated / 'Relations_0000.v')
    files.append(source / 'Spec.v')
    logs = run / 'coq-logs'
    logs.mkdir()
    command = ['bash', str(ROOT / 'environment/env.sh'), 'coqc', '-q',
               '-Q', str(support), 'ALCoq', '-Q', str(source), namespace]
    manifest['coq_sources'] = []
    for index, path in enumerate(files):
        manifest['coq_sources'].append({'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
        run_command(command + [str(path)], cwd=run, log=logs / f'{index:04d}-{path.stem}.log', manifest=manifest)
    manifest['coq_compiled'] = True


def verify_generation(source, backend_manifest, profile_name):
    """Reject partial inventories, duplicate bindings and changed emitted files."""
    source = Path(source).resolve()
    if backend_manifest.get('status') != 'coq-generated' or backend_manifest.get('code_generation_complete') is not True:
        raise ValueError('backend did not complete audited Coq generation')
    inventory = json.loads((source / 'inventory.json').read_text())
    if inventory.get('code_generation_complete') is not True:
        raise ValueError('inventory has no complete generation audit')
    declarations = inventory['declarations']
    if len(declarations) != inventory['declaration_count']:
        raise ValueError('declaration count differs from inventory')
    names = [d['generated_name'] for d in declarations]
    if len(names) != len(set(names)):
        raise ValueError('duplicate generated declaration')
    counts = {'generated-type': 0, 'generated-body': 0, 'consumed-metadata': 0}
    for declaration in declarations:
        expected = ('consumed-metadata' if declaration['namespace'] == 'var' else
                    'generated-type' if declaration['namespace'] == 'type' else 'generated-body')
        if declaration['disposition'] != expected:
            raise ValueError(f'unfinished or incorrect disposition: {declaration["source_name"]}')
        if expected == 'generated-body' and declaration.get('signature') is None:
            raise ValueError('generated body has no signature')
        counts[expected] += 1
    recorded = inventory['disposition_counts']
    if any(recorded.get(k) != n for k, n in counts.items()) or recorded.get('pending') != 0 or recorded.get('skipped') != 0:
        raise ValueError('declaration disposition coverage is incomplete')
    if recorded != backend_manifest.get('disposition_counts'):
        raise ValueError('backend and inventory disposition audits differ')
    bindings = backend_manifest['builtin_bindings']
    builtin_names = [d['source_name'] for d in declarations if d['kind'] == 'BuiltinDecD']
    bound_names = [b['source_name'] for b in bindings]
    expected_count = {'p4': 47, 'wasm': 76}[profile_name]
    if len(bound_names) != expected_count or len(set(bound_names)) != len(bound_names) or sorted(bound_names) != sorted(builtin_names):
        raise ValueError('builtin bindings do not exactly cover the pinned profile')
    if inventory['builtin_bindings'] != bindings:
        raise ValueError('backend and inventory builtin bindings differ')
    for binding in bindings:
        if binding['profile'] != profile_name or binding['declaration_kind'] != 'BuiltinDecD':
            raise ValueError('builtin binding profile or declaration kind mismatch')
        if not binding.get('runtime_helper') or not binding.get('runtime_source') or not binding.get('native_source'):
            raise ValueError('builtin binding has no concrete source/runtime mapping')
    outputs = backend_manifest['output_files']
    paths = [item['path'] for item in outputs]
    if len(paths) != len(set(paths)):
        raise ValueError('duplicate generated output path')
    actual = {str(path.relative_to(source)) for path in source.rglob('*.v')}
    if set(paths) != actual or 'Spec.v' not in actual:
        raise ValueError('generated output manifest does not exactly cover Coq files')
    for item in outputs:
        relative = Path(item['path'])
        if relative.is_absolute() or '..' in relative.parts or (relative != Path('Spec.v') and (len(relative.parts) != 2 or relative.parts[0] != 'Generated')):
            raise ValueError('unexpected generated publication path')
        unresolved = source / relative
        for ancestor in [unresolved, *unresolved.parents]:
            if ancestor == source.parent:
                break
            if ancestor.is_symlink():
                raise ValueError(f'generated output is a symlink: {ancestor}')
        path = owned_path(source, item['path'])
        if hashlib.sha256(path.read_bytes()).hexdigest() != item['sha256']:
            raise ValueError(f'generated output changed: {item["path"]}')
    return inventory


def publish_generated(source, profile_name, run, manifest):
    """Copy only compiled managed .v files; archive prior bytes before updates.

    Never move/delete an existing tree. Unknown differing files are rejected in
    a complete preflight before any destination file is written.
    """
    if manifest.get('coq_compiled') is not True or manifest.get('code_generation_complete') is not True:
        raise ValueError('publication requires complete generation and Coq compilation')
    source, run = Path(source).resolve(), Path(run).resolve()
    if not run.is_relative_to(STATE.resolve()):
        raise ValueError('publication evidence must be target-owned and ignored')
    if profile_name not in ['p4', 'wasm']:
        raise ValueError('unsupported publication profile')
    registry_path = owned_path(STATE, Path('publication') / f'{profile_name}.json')
    registry = json.loads(registry_path.read_text()) if registry_path.exists() else {}
    profile = {}
    destination = ROOT / 'specification' / profile_name
    prior = {item['path']: item for item in registry.get('managed_files', [])}
    plans = []
    for item in manifest['output_files']:
        relative = Path(item['path'])
        if relative.is_absolute() or '..' in relative.parts or (relative != Path('Spec.v') and (len(relative.parts) != 2 or relative.parts[0] != 'Generated')):
            raise ValueError('unexpected generated publication path')
        unresolved = source / relative
        for ancestor in [unresolved, *unresolved.parents]:
            if ancestor == source.parent:
                break
            if ancestor.is_symlink():
                raise ValueError(f'publication source is a symlink: {ancestor}')
        src = owned_path(source, relative)
        if hashlib.sha256(src.read_bytes()).hexdigest() != item['sha256']:
            raise ValueError('generated output changed before publication')
        target = destination / relative
        for ancestor in [target, *target.parents]:
            if ancestor == ROOT.parent:
                break
            if ancestor.is_symlink():
                raise ValueError(f'publication refuses a symlink: {ancestor}')
            if ancestor != target and ancestor.exists() and not ancestor.is_dir():
                raise ValueError(f'publication parent is not a directory: {ancestor}')
        owned_path(ROOT, target)
        previous = None
        if target.exists():
            if not target.is_file():
                raise ValueError(f'publication target is not a file: {target}')
            previous = hashlib.sha256(target.read_bytes()).hexdigest()
            if previous != item['sha256'] and item['path'] not in prior:
                raise ValueError(f'publication refuses unrelated differing file: {target}')
        if previous is not None and previous != item['sha256'] and (run / 'publication-archive' / profile_name / item['path']).exists():
            raise ValueError('publication archive already exists')
        plans.append((item, src, target, previous))
    publication = {'destination': str(destination), 'files': [], 'archived_files': [], 'retained_prior_managed_files': sorted(set(prior) - {p[0]['path'] for p in plans})}
    for item, src, target, previous in plans:
        if previous is not None and previous != item['sha256']:
            archive = run / 'publication-archive' / profile_name / item['path']
            archive.parent.mkdir(parents=True, exist_ok=True)
            if archive.exists():
                raise ValueError('publication archive already exists')
            shutil.copy2(target, archive)
            if hashlib.sha256(archive.read_bytes()).hexdigest() != previous:
                raise ValueError('publication archive did not preserve prior bytes')
            publication['archived_files'].append({'path': str(target), 'archive': str(archive), 'sha256': previous})
        target.parent.mkdir(parents=True, exist_ok=True)
        if previous != item['sha256']:
            shutil.copy2(src, target)
        if hashlib.sha256(target.read_bytes()).hexdigest() != item['sha256']:
            raise ValueError('published source hash mismatch')
        publication['files'].append(dict(item))
    manifest['publication'] = publication
    for item in publication['files']:
        prior[item['path']] = dict(item)
    profile['publication'] = {'destination': str(destination.relative_to(ROOT)), 'managed_files': sorted(prior.values(), key=lambda item: item['path']), 'last_verified_run': str(run.relative_to(ROOT))}
    registry_path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8',
            prefix=f'.{profile_name}-', dir=registry_path.parent, delete=False) as stream:
        temporary = Path(stream.name)
        json.dump(profile['publication'], stream, indent=2)
        stream.write('\n')
    try:
        temporary.replace(registry_path)
    finally:
        temporary.unlink(missing_ok=True)
    return profile


def record_results(profile_name, backend_manifest, manifest, publication_profile=None):
    """Keep derived bindings and validation beside the run, never in input profiles."""
    run = owned_path(STATE, Path(manifest['run']))
    result = {
        'profile': profile_name,
        'builtin_bindings': backend_manifest['builtin_bindings'],
        'builtin_bindings_status': 'validated-actual-al-and-implemented',
        'validation': {
            'source_hashes': 'verified', 'al_conversion': 'verified',
            'coq_generation': 'verified',
            'coq_compilation': 'verified' if manifest.get('coq_compiled') else 'not-run',
            'last_evidence': str(run.relative_to(ROOT)),
        },
    }
    if publication_profile is not None:
        result['publication'] = publication_profile['publication']
    write_json(run / 'profile-results.json', result)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=['p4', 'wasm'])
    parser.add_argument('--inventory', action='store_true', help='collect AL declarations without claiming translation')
    parser.add_argument('--check', action='store_true', help='require full translation and Coq compilation')
    parser.add_argument('--inductive-relations', action='store_true',
                        help='emit direct relation definitions for supported Actions')
    args = parser.parse_args(argv)
    if args.inventory and args.check:
        parser.error('--inventory and --check are mutually exclusive')
    if args.inventory and args.inductive_relations:
        parser.error('--inventory and --inductive-relations are mutually exclusive')
    (STATE / 'logs').mkdir(parents=True, exist_ok=True)
    run = Path(tempfile.mkdtemp(prefix=f'translate-{args.profile}-', dir=STATE / 'logs'))
    manifest = {'schema_version': 1, 'profile': args.profile, 'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'mode': 'inventory' if args.inventory else 'check' if args.check else 'translation', 'inductive_relations': args.inductive_relations, 'status': 'started', 'commands': [], 'coq_compiled': False, 'code_generation_complete': False, 'translation_complete': False, 'run': str(run)}
    try:
        profile_path = ROOT / 'translator/profiles' / f'{args.profile}.json'
        profile = json.loads(profile_path.read_text())
        if profile['schema_version'] != 1 or profile['name'] != args.profile:
            raise ValueError('unsupported or mismatched profile')
        paths = verify_inputs(ROOT, profile)
        source = owned_path(ROOT, profile['frontend']['source_root'])
        archive = owned_path(ROOT, profile['frontend']['archive'])
        if hashlib.sha256(archive.read_bytes()).hexdigest() != profile['frontend']['archive_sha256']:
            raise ValueError('frontend archive SHA-256 mismatch')
        # Verify the source tree against the pinned archive before copying it.
        import tarfile
        with tarfile.open(archive) as tar:
            for member in tar.getmembers():
                if member.isfile():
                    archived = tar.extractfile(member).read()
                    extracted = owned_path(source, member.name)
                    if not extracted.is_file() or hashlib.sha256(extracted.read_bytes()).digest() != hashlib.sha256(archived).digest():
                        raise ValueError(f'frontend source differs from archive: {member.name}')
        shutil.copy2(profile_path, run / 'profile.json')
        manifest['inputs'] = profile['inputs']
        manifest['frontend'] = profile['frontend']
        build, backend = prepare_backend(source, run)
        manifest['build_root'] = str(build)
        manifest['backend_sources'] = [{'path': str(path.relative_to(backend)), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
                                       for path in sorted(backend.iterdir()) if path.suffix == '.ml' or path.name == 'dune']
        env = ['bash', str(ROOT / 'environment/env.sh'), 'frontend']
        run_command(env + ['ocamlc', '-version'], cwd=ROOT, log=run / 'frontend-version.log', manifest=manifest)
        manifest['versions'] = {'frontend_ocaml': (run / 'frontend-version.log').read_text().strip()}
        run_command(env + ['dune', 'build', '--root', str(build), '-j', os.environ.get('JOBS', '2'), 'p4spec/al_to_coq/main.exe'], cwd=ROOT, log=run / 'build.log', manifest=manifest)
        executable = build / '_build/default/p4spec/al_to_coq/main.exe'
        output = run / ('inventory' if args.inventory else 'spec')
        output.mkdir()
        command = [str(executable), '--profile', args.profile, '--output', str(output), '--manifest', str(run / 'backend-manifest.json')]
        for path in paths:
            command += ['--input', str(path)]
        if args.inventory:
            command += ['--inventory']
        if args.inductive_relations:
            command += ['--inductive-relations']
        run_command(env + command, cwd=ROOT, log=run / 'frontend.log', manifest=manifest)
        if args.inventory:
            manifest['status'] = 'inventory-complete'
            print(f'AL inventory: {output / "inventory.json"}')
        else:
            backend_manifest = json.loads((run / 'backend-manifest.json').read_text())
            inventory = verify_generation(output, backend_manifest, args.profile)
            manifest['code_generation_complete'] = True
            for key in ['output_files', 'builtin_bindings', 'disposition_counts']:
                manifest[key] = backend_manifest[key]
            manifest['al_declaration_count'] = inventory['declaration_count']
            manifest['runtime_sources'] = [
                {'path': str(path.relative_to(ROOT)), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
                for path in sorted((ROOT / 'translator/coq').rglob('*.v'))]
            if args.check:
                run_command(['bash', str(ROOT / 'environment/env.sh'), 'coqc', '--version'], cwd=ROOT, log=run / 'coq-version.log', manifest=manifest)
                manifest['versions']['coq'] = (run / 'coq-version.log').read_text().strip()
                compile_generated(output, args.profile, run, manifest)
                verify_generation(output, backend_manifest, args.profile)
                verify_inputs(ROOT, profile)
                for entry in manifest['runtime_sources']:
                    current = owned_path(ROOT, entry['path'])
                    copied = run / 'support' / Path(entry['path']).relative_to('translator/coq')
                    if (hashlib.sha256(current.read_bytes()).hexdigest() != entry['sha256'] or
                            hashlib.sha256(copied.read_bytes()).hexdigest() != entry['sha256']):
                        raise ValueError(f'runtime source changed during compilation: {entry["path"]}')
                publication_profile = publish_generated(output, args.profile, run, manifest)
                manifest['translation_complete'] = True
                inventory.update({'coq_compiled': True, 'translation_complete': True, 'stage': 'Coq-compiled'})
                write_json(output / 'inventory.json', inventory)
                record_results(args.profile, backend_manifest, manifest, publication_profile)
            else:
                record_results(args.profile, backend_manifest, manifest)
            manifest['status'] = 'checked' if args.check else 'coq-generated'
            print(f'Coq source evidence: {output}')
        return 0
    except (ValueError, KeyError, OSError, RuntimeError) as error:
        manifest['status'] = 'failed'
        manifest['error'] = str(error)
        print(f'{error}\nEvidence: {run}', file=sys.stderr)
        return 1
    finally:
        write_json(run / 'manifest.json', manifest)


if __name__ == '__main__':
    sys.exit(main())
