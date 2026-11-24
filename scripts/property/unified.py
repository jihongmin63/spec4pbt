"""Prepare and execute a single property declaration with shared setup."""
from collections import Counter
from dataclasses import asdict, dataclass, replace
import json
from pathlib import Path
import re
import subprocess
import tempfile

from .bridge import ROOT, pinned_source_digest
from .compiler import (attach_implementation, compile_debug, compile_replay,
                       compile_spec)
from .context import (CONTEXT, establish_context, file_hash, load_context,
                      validate_hashes)
from .debug import debug
from .generation import GenerationError, derive_and_sample
from .model import CompileError
from .replay import replay
from .setup import load_implementation, load_specification


@dataclass(frozen=True)
class PreparedProperty:
    model: object
    publication: Path
    specification: object
    context: dict


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


def write_source_once(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        with path.open('x') as stream:
            stream.write(text)
    except FileExistsError:
        if path.read_text() != text:
            raise ValueError(f'fixed source differs: {path}')


def initial_candidate(prop, original, namespace):
    candidate = prop / 'candidates/v001'
    if candidate.exists():
        return
    start = original.index('Inductive predicate')
    end = original.index('\n\n', start)
    header = ('Require Import Property.Original.\n'
              'From Coq Require Import String Ascii ZArith.\n'
              'From ALCoq Require Import Execution.\n'
              f'From {namespace}.Generated Require Import Types_0000 InductiveRelations.\n')
    write_source_once(candidate / 'Candidate.v', header + original[start:end] + '\n')
    write_source_once(candidate / 'Equivalence.v', '''Require Import Property.Original Property.candidates.v001.Candidate.
Theorem equivalent : forall x : Original.Input,
  Original.predicate x <-> Candidate.predicate x.
Proof.
  intro x; split; intro H; destruct H; econstructor; eassumption.
Qed.
''')


def prepare_property(property_dir, specification_manifest=None):
    """Create checked fixed artifacts once; subsequent calls validate their identity."""
    from .declaration import lower_property
    from .rocq import render_original, translate_property
    prop = Path(property_dir).resolve()
    if not prop.is_relative_to(ROOT) or not re.fullmatch(r'[A-Za-z0-9_][A-Za-z0-9_-]*', prop.name):
        raise ValueError('property directory must have a simple name inside this worktree')
    context = load_context(prop)
    if context is None:
        if specification_manifest is None:
            raise CompileError('first prepare requires --spec Specification.toml')
        if (prop / 'Property.toml').exists():
            raise CompileError('prepare the unified declaration in a new property directory')
        specification = load_specification(specification_manifest)
        runs = prop / '.runs'
        runs.mkdir(exist_ok=True)
        staging = Path(tempfile.mkdtemp(prefix='declaration-', dir=runs))
        property_source = prop / 'Property.spectec'
        authored_hashes = {**specification.hashes, str(property_source): file_hash(property_source)}
        lowered = lower_property(property_source, list(specification.sources), staging)
        validate_hashes(authored_hashes)
        publication = specification.manifest.parent / 'properties' / prop.name
        try:
            # Diagnose unsupported property forms before the translator snapshots
            # the input, so these errors retain the authored source mapping.
            compile_spec(lowered.source, lowered.config)
            translate_property(lowered.source, lowered.config, publication,
                               profile=specification.profile)
            original = render_original(lowered.source, lowered.config, publication=publication,
                                       public_input_names=lowered.source_map.get('variables', {}))
        except (CompileError, RuntimeError, ValueError) as error:
            from .declaration import remap_locations
            mapping = dict(lowered.source_map)
            rows = list(mapping['lines'])
            # Both existing translation passes use a private copy of the same
            # bytes. Alias diagnostic locations in that copy to the source map.
            for path in set(re.findall(r'(/[^\s:]+/' + re.escape(lowered.source.name) +
                                       r')(?=:\d)', str(error))):
                rows.extend({**row, 'generated_file': path} for row in mapping['lines']
                            if row['generated_file'] == str(lowered.source))
            mapping['lines'] = rows
            raise CompileError(remap_locations(str(error), mapping),
                               code=getattr(error, 'code', 'property_translation_error'),
                               details=remap_locations(getattr(error, 'details', None), mapping)) from error
        validate_hashes(authored_hashes)
        write_source_once(prop / 'Original.v', original)
        initial_candidate(prop, original, specification.namespace)
        hashes = {**authored_hashes, **publication_hashes(publication),
                  str(prop / 'Original.v'): file_hash(prop / 'Original.v'),
                  str(lowered.source.resolve()): file_hash(lowered.source),
                  str(lowered.config.resolve()): file_hash(lowered.config)}
        context = establish_context(prop, {
            'version': 2, 'property': str(prop), 'name': lowered.name,
            'specification': str(specification.manifest),
            'publication': str(publication.resolve()),
            'source': str(lowered.source.resolve()), 'config': str(lowered.config.resolve()),
            'source_map': lowered.source_map, 'semantic_hashes': hashes})
    specification = load_specification(context['specification'])
    if specification_manifest is not None:
        selected = load_specification(specification_manifest)
        if selected.manifest != specification.manifest:
            raise CompileError('selected specification differs from fixed property context')
    model = compile_spec(context['source'], context['config'])
    names = context['source_map'].get('variables', {})
    model = replace(model, inputs=tuple({**item, 'name': names.get(item['name'], item['name'])}
                                        for item in model.inputs),
                    source_map=context['source_map'], semantic_hashes=context['semantic_hashes'])
    return PreparedProperty(model, Path(context['publication']), specification, context)


def tool_hashes():
    paths = [ROOT / 'environment/env.sh', ROOT / 'environment/opam-switch.export',
             ROOT / 'scripts/check.py', ROOT / 'scripts/run.py', ROOT / 'scripts/translate.py']
    for directory, pattern in [('scripts/property', '*.py'), ('property/bridge', '*.ml'),
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


def execute(args):
    """CLI entry point for declarations; legacy evidence uses the legacy path."""
    prop = Path(args.property).resolve()
    if not prop.is_relative_to(ROOT):
        raise ValueError('property must be inside this worktree')
    runs = prop / '.runs'
    runs.mkdir(parents=True, exist_ok=True)
    evidence = Path(tempfile.mkdtemp(prefix=args.action + '-', dir=runs))
    report = {'version': 2, 'action': args.action, 'property': str(prop),
              'status': 'running', 'generator_proof': 'not_checked'}
    model = None
    try:
        prepared = prepare_property(prop, getattr(args, 'spec', None))
        model = prepared.model
        tools = tool_hashes()
        report.update(input_fields=list(model.inputs),
                      semantic_hashes=prepared.context['semantic_hashes'],
                      tool_hashes=tools, publication=str(prepared.publication),
                      property_name=prepared.context['name'],
                      fixed_original=str(runs / 'fixed-original-v2.json'))
        is_replay = args.action == 'replay' or (
            args.action == 'prepare' and args.target == 'replay')
        implementation = None
        if is_replay:
            if getattr(args, 'implementation', None) is None:
                raise CompileError('replay requires --implementation Adapter.toml')
            implementation = load_implementation(args.implementation, prepared.specification)
            model = attach_implementation(model, implementation)
            report['implementation_hashes'] = dict(implementation.hashes)
        if args.action == 'prepare':
            report['target'] = args.target
            if args.target == 'replay':
                program = compile_replay(model)
                report['analysis'] = program.analysis
            elif args.target == 'debug':
                program = compile_debug(model)
                report.update(debug_available=program.available,
                              missing_definitions=list(program.missing), al_md5=program.al_md5)
        elif args.action == 'sample':
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
            report.update(attempts=len(batch.samples),
                          generated=sum(item is not None for item in batch.samples),
                          no_generation=sum(item is None for item in batch.samples),
                          samples_file=str(path), derivation_report=str(batch.report))
        else:
            values, batch_path = load_inputs(args, prop, prepared, tools)
            report.update(batch_evidence=batch_path, attempts=len(values))
            if is_replay:
                program = compile_replay(model)
                report['analysis'] = program.analysis
                run_one = lambda value: replay(program, value, implementation.commands,
                                                timeout=args.timeout)
            else:
                program = compile_debug(model)
                report.update(debug_available=program.available, al_md5=program.al_md5)
                run_one = lambda value: debug(program, value, timeout=args.timeout)
            results = []
            for index, value in enumerate(values):
                if value is None:
                    results.append({'attempt': index, 'status': 'no_generation'})
                else:
                    results.append({'attempt': index, 'input': value, **asdict(run_one(value))})
            path = evidence / 'results.json'
            path.write_text(json.dumps(results, indent=2) + '\n')
            report.update(results_file=str(path),
                          status_counts=dict(Counter(item['status'] for item in results)),
                          external_calls=sum(item.get('external_call_count', 0) for item in results))
            if batch_path is not None:
                load_inputs(args, prop, prepared, tools)
        load_context(prop)
        if tools != tool_hashes():
            raise ValueError('tools changed during command')
        if implementation is not None:
            validate_hashes(implementation.hashes)
        report['status'] = 'passed'
    except (CompileError, GenerationError, OSError, ValueError, RuntimeError,
            KeyError, subprocess.TimeoutExpired) as error:
        report.update(status='failed', error=str(error))
        if isinstance(error, CompileError):
            report['compile_error_code'] = error.code
            if error.details is not None:
                report['analysis_failure'] = error.details
    if model is not None and model.source_map:
        from .declaration import remap_locations
        for key in ('analysis', 'analysis_failure', 'error'):
            if key in report:
                report[key] = remap_locations(report[key], model.source_map)
    path = evidence / 'result.json'
    path.write_text(json.dumps(report, indent=2) + '\n')
    return path, report['status'] == 'passed'
