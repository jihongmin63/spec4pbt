"""Compatibility for fixed properties with explicit Pre/Goal and Property.toml."""
from collections import Counter
from dataclasses import asdict
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile

from .bridge import BRIDGE, ROOT, pinned_source_digest
from .compiler import CompileError, compile_debug, compile_replay, compile_spec
from .debug import debug
from .generation import GenerationError, derive_and_sample
from .replay import replay


def file_hash(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def original_files(property_dir):
    """Sources that define the fixed original, excluding candidate additions."""
    specification = ROOT / 'specification' / property_dir.name
    files = [property_dir / filename for filename in
             ('Property.spectec', 'Property.toml', 'Original.v')]
    files += [specification / 'source/Property.watsup']
    files += [path for path in specification.rglob('*')
              if path.is_file()
              and path.relative_to(specification).parts[0] != 'candidates'
              and path.suffix in ('.v', '.watsup', '.spectec')]
    return sorted(set(files))


def original_hashes(property_dir):
    return {str(path.relative_to(ROOT)): file_hash(path)
            for path in original_files(property_dir)}


def ensure_fixed_original(property_dir, hashes, *, create=False):
    """Validate or atomically establish the immutable original-source manifest."""
    baseline = property_dir / '.runs/fixed-original.json'
    if not baseline.exists():
        if not create:
            return None
        if original_hashes(property_dir) != hashes:
            raise ValueError('fixed original changed during preparation')
        with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8',
                prefix='.fixed-original-', dir=baseline.parent, delete=False) as stream:
            temporary = Path(stream.name)
            json.dump({'version': 1, 'hashes': hashes}, stream, indent=2, sort_keys=True)
            stream.write('\n')
        try:
            temporary.chmod(0o444)
            try:
                os.link(temporary, baseline)
            except FileExistsError:
                pass
        finally:
            temporary.unlink()
    manifest = json.loads(baseline.read_text())
    if (not isinstance(manifest, dict) or manifest.get('version') != 1
            or not isinstance(manifest.get('hashes'), dict)):
        raise ValueError(f'invalid fixed original manifest: {baseline}')
    expected = manifest['hashes']
    changed = sorted(path for path in expected.keys() | hashes.keys()
                     if expected.get(path) != hashes.get(path))
    if changed:
        raise ValueError('fixed original changed: ' + ', '.join(changed))
    return baseline


def fixed_files(property_dir):
    specification = ROOT / 'specification' / property_dir.name
    files = original_files(property_dir)
    files += sorted((property_dir / 'candidates').glob('v*/Helper.watsup'))
    files += sorted(specification.rglob('*.v'))
    files += sorted(specification.rglob('PassEvidence.json'))
    for manifest in specification.rglob('PassEvidence.json'):
        evidence = json.loads(manifest.read_text())
        dependencies = [entry['path'] for entry in evidence.get('artifacts', [])]
        if 'source' in evidence:
            dependencies.append(evidence['source'])
        for relative in dependencies:
            path = (manifest.parent / relative).resolve()
            if not path.is_relative_to(ROOT):
                raise ValueError(f'semantic pass dependency escapes worktree: {path}')
            if not path.is_file():
                raise ValueError(f'missing semantic pass dependency: {path}')
            files.append(path)
    files += sorted(BRIDGE.glob('*.ml'))
    files += sorted((ROOT / 'scripts/property').glob('*.py'))
    files += sorted((ROOT / 'translator/src').glob('*.ml'))
    files += [ROOT / 'environment/env.sh', ROOT / 'environment/opam-switch.export']
    return sorted({path for path in files if path.is_file()})


def fixed_hashes(property_dir):
    hashes = {str(path.relative_to(ROOT)): file_hash(path)
              for path in fixed_files(property_dir)}
    hashes['pinned/p4-spectec-source'] = pinned_source_digest()
    return hashes


def source_for(property_dir):
    return ROOT / 'specification' / property_dir.name / 'source/Property.watsup'


def model_for(property_dir):
    source = source_for(property_dir)
    property_source = property_dir / 'Property.spectec'
    if property_source.read_bytes() != source.read_bytes():
        raise CompileError('fixed Property.spectec differs from translated source')
    return compile_spec(source, property_dir / 'Property.toml')


def new_evidence(property_dir, action):
    directory = property_dir / '.runs'
    directory.mkdir(exist_ok=True)
    return Path(tempfile.mkdtemp(prefix=action + '-', dir=directory))


def read_inputs(args, property_dir, hashes):
    if args.input_json:
        return [json.loads(args.input_json)], None
    if not args.samples_file:
        raise ValueError('provide --samples-file or --input-json')
    samples = Path(args.samples_file).resolve()
    if not samples.is_relative_to(property_dir / '.runs'):
        raise ValueError('samples file must be property-local evidence')
    batch = samples.parent / 'batch.json'
    if not batch.is_file():
        raise ValueError('samples file has no batch evidence')
    provenance = json.loads(batch.read_text())
    if provenance['fixed_hashes'] != hashes:
        raise ValueError('fixed source changed since sampling')
    if file_hash(samples) != provenance['samples_sha256']:
        raise ValueError('samples changed since generation')
    return json.loads(samples.read_text()), str(batch)


def execute(args):
    property_dir = args.property.resolve()
    if not property_dir.is_relative_to(ROOT / 'properties'):
        raise ValueError('property must be inside this worktree')
    evidence = new_evidence(property_dir, args.action)
    report = {'action': args.action, 'status': 'running',
              'property': str(property_dir), 'fixed_hashes': fixed_hashes(property_dir),
              'generator_proof': 'not_checked'}
    try:
        originals = original_hashes(property_dir)
        ensure_fixed_original(property_dir, originals)
        model = model_for(property_dir)
        baseline = ensure_fixed_original(property_dir, originals, create=True)
        report['fixed_original'] = {'manifest': str(baseline),
                                    'sha256': file_hash(baseline)}
        report['input_fields'] = list(model.inputs)
        if args.action == 'prepare':
            if args.target == 'replay':
                program = compile_replay(model)
                report['analysis'] = program.analysis
            elif args.target == 'debug':
                program = compile_debug(model)
                report['debug_available'] = program.available
                report['missing_definitions'] = list(program.missing)
                report['al_md5'] = program.al_md5
            report['target'] = args.target
        elif args.action == 'sample':
            batch = derive_and_sample(property_dir, args.candidate, model.inputs,
                                      count=args.count, size=args.size, seed=args.seed,
                                      type_schema=model.type_schema)
            samples = list(batch.samples)
            sample_path = evidence / 'samples.json'
            sample_path.write_text(json.dumps(samples, indent=2) + '\n')
            (evidence / 'batch.json').write_text(json.dumps({
                'candidate': args.candidate,
                'derivation_report': str(batch.report),
                'fixed_hashes': report['fixed_hashes'],
                'samples_sha256': file_hash(sample_path),
                'seed': args.seed, 'size': args.size}, indent=2) + '\n')
            report.update(attempts=len(samples), generated=sum(x is not None for x in samples),
                          no_generation=sum(x is None for x in samples),
                          samples_file=str(sample_path),
                          derivation_report=str(batch.report))
        else:
            samples, batch_path = read_inputs(args, property_dir, report['fixed_hashes'])
            report['batch_evidence'] = batch_path
            report['attempts'] = len(samples)
            if args.action == 'replay':
                program = compile_replay(model)
                report['analysis'] = program.analysis
                commands = {}
                adapter_hashes = {}
                for contract in model.external:
                    adapter = contract['adapter']
                    path = ROOT / 'adapters' / property_dir.name / (adapter + '.py')
                    if not path.is_file():
                        raise ValueError(f'missing adapter: {path}')
                    commands[adapter] = [sys.executable, str(path)]
                    adapter_hashes[str(path.relative_to(ROOT))] = file_hash(path)
                report['adapter_hashes'] = adapter_hashes
                execute_one = lambda sample: replay(program, sample, commands,
                                                    timeout=args.timeout)
            else:
                program = compile_debug(model)
                report['debug_available'] = program.available
                report['al_md5'] = program.al_md5
                execute_one = lambda sample: debug(program, sample,
                                                   timeout=args.timeout)
            results = []
            for index, sample in enumerate(samples):
                if sample is None:
                    results.append({'attempt': index, 'status': 'no_generation'})
                    continue
                result = execute_one(sample)
                results.append({'attempt': index, 'input': sample,
                                **asdict(result)})
            (evidence / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
            report['status_counts'] = dict(Counter(item['status'] for item in results))
            report['external_calls'] = sum(item.get('external_call_count', 0)
                                           for item in results)
            report['results_file'] = str(evidence / 'results.json')
        if report['fixed_hashes'] != fixed_hashes(property_dir):
            raise ValueError('fixed source changed during command')
        report['status'] = 'passed'
    except (CompileError, GenerationError, OSError, ValueError) as error:
        report['status'] = 'failed'
        report['error'] = str(error)
        if isinstance(error, CompileError):
            report['compile_error_code'] = error.code
        if isinstance(error, CompileError) and error.details is not None:
            report['analysis_failure'] = error.details
    (evidence / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
    return evidence / 'result.json', report['status'] == 'passed'
