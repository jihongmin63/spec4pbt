"""Run the checked tactic derivation and load Input-only samples."""
from dataclasses import dataclass
from pathlib import Path
import json
import re
import subprocess
import sys

from .bridge import ROOT
from .codec import CodecError, decode_input
from .coq_codec import constructor_schema


class GenerationError(RuntimeError):
    pass


@dataclass(frozen=True)
class GenerationBatch:
    candidate: str
    samples: tuple[dict | None, ...]
    report: Path
    seed: int
    size: int


def load_samples(samples, fields, type_schema=None):
    if not isinstance(samples, list):
        raise GenerationError('samples must be a list')
    try:
        constructors = constructor_schema({} if type_schema is None else type_schema)
    except CodecError as error:
        raise GenerationError(str(error)) from error
    output = []
    for index, sample in enumerate(samples):
        if sample is None:
            output.append(None)
            continue
        try:
            output.append(decode_input(sample, fields, constructors))
        except CodecError as error:
            raise GenerationError(f'sample {index}: {error}') from error
    return output


def derive_and_sample(property_dir, candidate, fields, *, type_schema=None, count=100,
                      size=30, seed=0, timeout=360):
    property_dir = Path(property_dir).resolve()
    command = [sys.executable, str(ROOT / 'scripts/run.py'), str(property_dir),
               '--candidate', candidate, '--samples', str(count),
               '--size', str(size), '--seed', str(seed)]
    result = subprocess.run(command, cwd=ROOT, capture_output=True,
                            text=True, timeout=timeout)
    if result.returncode:
        raise GenerationError(result.stdout + result.stderr)
    matched = re.search(r'(/\S+/\.runs/run-[^\s]+/result\.json)', result.stdout)
    if not matched:
        raise GenerationError('run.py did not report evidence')
    report = Path(matched.group(1)).resolve()
    if not report.is_relative_to(property_dir / '.runs'):
        raise GenerationError('run.py reported evidence outside property')
    evidence = json.loads(report.read_text())
    if evidence.get('status') != 'passed' or evidence.get('candidate') != candidate:
        raise GenerationError('candidate derivation did not pass')
    samples = load_samples(json.loads((report.parent / 'samples.json').read_text()),
                           fields, type_schema)
    return GenerationBatch(candidate, tuple(samples), report, seed, size)


def sample(args, prepared, evidence, tools):
    """Verify the selected prefix, derive inputs, and record a reusable batch."""
    from .context import CONTEXT, candidate_hashes, candidate_snapshot, file_hash
    prop = Path(args.property).resolve()
    runs = prop / '.runs'
    model = prepared.model
    candidate_inputs, snapshot = candidate_snapshot(prop, args.candidate)
    batch = derive_and_sample(prop, args.candidate, model.inputs,
                              type_schema=model.type_schema, count=args.count,
                              size=args.size, seed=args.seed)
    derivation = json.loads(batch.report.read_text())
    if derivation['source_hashes'] != snapshot.report['source_hashes']:
        raise ValueError('candidate sources changed between snapshot and derivation')
    if candidate_inputs != candidate_hashes(prop, args.candidate):
        raise ValueError('candidate changed during sampling')
    path = evidence / 'samples.json'
    path.write_text(json.dumps(list(batch.samples), indent=2) + '\n')
    (evidence / 'batch.json').write_text(json.dumps({
        'version': 2, 'candidate': args.candidate,
        'candidate_hashes': candidate_inputs,
        'semantic_hashes': prepared.context['semantic_hashes'],
        'tool_hashes': tools, 'context_sha256': file_hash(runs / CONTEXT),
        'samples_sha256': file_hash(path), 'derivation_report': str(batch.report),
        'source_snapshot': str(snapshot.directory / 'result.json'),
        'derivation_source_hashes': derivation['source_hashes'],
        'seed': args.seed, 'size': args.size}, indent=2) + '\n')
    return dict(attempts=len(batch.samples),
                  generated=sum(item is not None for item in batch.samples),
                  no_generation=sum(item is None for item in batch.samples),
                  samples_file=str(path), derivation_report=str(batch.report))
