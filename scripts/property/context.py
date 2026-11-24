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
