"""Validate the generated connection between a property and its publication."""
import hashlib
import json
import os
from pathlib import Path
import tempfile

ROOT = Path(__file__).resolve().parents[2]
CONTEXT = 'property-context.json'
BASELINE = 'fixed-original-v2.json'


def file_hash(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def checked_path(value):
    if not isinstance(value, str):
        raise ValueError('invalid property context path')
    path = Path(value).resolve()
    if not path.is_relative_to(ROOT):
        raise ValueError(f'property context path escapes worktree: {path}')
    return path


def validate_hashes(hashes):
    if not isinstance(hashes, dict) or not hashes:
        raise ValueError('invalid property semantic hashes')
    for value, expected in hashes.items():
        path = checked_path(value)
        if not path.is_file() or file_hash(path) != expected:
            raise ValueError(f'fixed original changed: {path}')


def load_context(property_dir):
    prop = Path(property_dir).resolve()
    path = prop / '.runs' / CONTEXT
    if not path.exists():
        if (prop / '.runs' / BASELINE).exists():
            raise ValueError('fixed property context is missing')
        return None
    baseline = json.loads((prop / '.runs' / BASELINE).read_text())
    if baseline.get('version') != 2 or baseline.get('context_sha256') != file_hash(path):
        raise ValueError('fixed property context changed')
    context = json.loads(path.read_text())
    if context.get('version') != 2 or context.get('property') != str(prop):
        raise ValueError('invalid property context identity')
    for key in ('publication', 'source', 'config', 'specification'):
        checked_path(context[key])
    hashes = context.get('semantic_hashes')
    if baseline.get('hashes') != hashes:
        raise ValueError('fixed property semantic identity changed')
    validate_hashes(hashes)
    required = [prop / 'Original.v', prop / 'Property.spectec',
                Path(context['source']), Path(context['config']),
                Path(context['specification']), Path(context['publication']) / 'PassEvidence.json']
    if any(str(p.resolve()) not in hashes for p in required):
        raise ValueError('incomplete property semantic identity')
    return context


def write_once(path, value):
    """Publish complete JSON without overwriting an existing fixed record."""
    path = Path(path)
    data = json.dumps(value, indent=2, sort_keys=True) + '\n'
    with tempfile.NamedTemporaryFile(mode='w', dir=path.parent, delete=False) as stream:
        stream.write(data)
        temporary = Path(stream.name)
    try:
        try:
            os.link(temporary, path)
        except FileExistsError:
            if path.read_text() != data:
                raise ValueError(f'fixed record differs: {path}')
    finally:
        temporary.unlink()


def establish_context(property_dir, context):
    runs = Path(property_dir) / '.runs'
    runs.mkdir(exist_ok=True)
    validate_hashes(context['semantic_hashes'])
    path = runs / CONTEXT
    write_once(path, context)
    write_once(runs / BASELINE, {'version': 2, 'context_sha256': file_hash(path),
                                'hashes': context['semantic_hashes']})
    return load_context(property_dir)


def publication_hashes(publication):
    manifest = publication / 'PassEvidence.json'
    evidence = json.loads(manifest.read_text())
    paths = [manifest, *(path for path in publication.rglob('*.v')
                         if path.relative_to(publication).parts[0] != 'candidates')]
    if evidence.get('source'):
        source = (publication / evidence['source']).resolve()
        if not source.is_relative_to(ROOT):
            raise ValueError('publication source escapes worktree')
        paths.append(source)
    for item in evidence['artifacts']:
        path = (publication / item['path']).resolve()
        if not path.is_relative_to(publication.resolve()):
            raise ValueError('publication artifact escapes its directory')
        paths.append(path)
    return {str(path.resolve()): file_hash(path) for path in paths}


def tool_hashes():
    from .bridge import pinned_source_digest
    paths = [ROOT / 'environment/env.sh', ROOT / 'environment/opam-switch.export',
             ROOT / 'scripts/check.py', ROOT / 'scripts/run.py', ROOT / 'scripts/translate.py']
    for directory, pattern in [('scripts/property', '*.py'), ('scripts/property/native', '*.ml'),
                               ('translator/src', '*.ml'), ('translator/coq', '*.v')]:
        paths.extend((ROOT / directory).rglob(pattern))
    result = {str(path): file_hash(path) for path in sorted(set(paths))}
    result['pinned/p4-spectec-source'] = pinned_source_digest()
    return result


def candidate_snapshot(prop, candidate):
    """Use the checker's own publication/import resolver and preserve its evidence."""
    from scripts.check import CheckError, Session
    session = None
    try:
        session = Session(prop, candidate)
        session.report.update(action='source_snapshot', verification='source_identity_only')
        session.snapshot_inputs()
        session.fresh()
        hashes = {str(path): digest for path, digest in session.originals.items()}
        # Preserve selected publication identities even for generated modules
        # outside the imported closure, as in the original batch contract.
        context = session.property_context
        if context:
            for name in session.sequence:
                publication = Path(context['publication']) / 'candidates' / name
                if publication.exists():
                    hashes.update(publication_hashes(publication))
        for name in session.sequence:
            helper = prop / 'candidates' / name / 'Helper.watsup'
            if helper.exists():
                hashes[str(helper)] = file_hash(helper)
        session.finish()
        return hashes, session
    except (CheckError, OSError, ValueError) as error:
        if session is not None:
            session.finish(error)
        raise ValueError(str(error)) from error


def candidate_hashes(prop, candidate):
    return candidate_snapshot(prop, candidate)[0]


def load_inputs(args, prop, prepared, tools):
    if args.input_json is not None:
        return [json.loads(args.input_json)], None
    if args.samples_file is None:
        raise ValueError('provide --samples-file or --input-json')
    samples = Path(args.samples_file).resolve()
    if not samples.is_relative_to(prop / '.runs'):
        raise ValueError('samples file must be property-local evidence')
    path = samples.parent / 'batch.json'
    batch = json.loads(path.read_text())
    if batch.get('version') != 2:
        raise ValueError('samples require a unified property batch')
    if batch['semantic_hashes'] != prepared.context['semantic_hashes']:
        raise ValueError('fixed source changed since sampling')
    if batch['tool_hashes'] != tools:
        raise ValueError('tools changed since sampling')
    if batch['context_sha256'] != file_hash(prop / '.runs' / CONTEXT):
        raise ValueError('property context changed since sampling')
    try:
        current_candidate = candidate_hashes(prop, batch['candidate'])
    except ValueError as error:
        raise ValueError(f'candidate changed since sampling: {error}') from error
    if batch['candidate_hashes'] != current_candidate:
        raise ValueError('candidate changed since sampling')
    if batch['samples_sha256'] != file_hash(samples):
        raise ValueError('samples changed since generation')
    values = json.loads(samples.read_text())
    if not isinstance(values, list):
        raise ValueError('samples must be a list')
    return values, str(path)
