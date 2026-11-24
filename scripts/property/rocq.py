"""Publish typed property premises through the existing SpecTec to Coq backend."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import tempfile
import tomllib
import fcntl

from scripts import translate
from .bridge import ROOT, PINNED, build_bridge, pinned_source_digest


STATE = ROOT / '_opam-testing-theorems'


def build_backend():
    parent = STATE / 'build'
    parent.mkdir(parents=True, exist_ok=True)
    with (parent / 'property-translator.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        return _build_backend()


def _build_backend():
    sources = sorted((ROOT / 'translator/src').glob('*.ml')) + [ROOT / 'translator/src/dune']
    key = hashlib.sha256(b''.join(p.read_bytes() for p in sources) +
                         pinned_source_digest().encode()).hexdigest()[:20]
    build = STATE / 'build' / ('property-translator-' + key)
    pointer = build / 'executable.txt'
    if pointer.is_file() and Path(pointer.read_text().strip()).is_file():
        return Path(pointer.read_text().strip())
    build.mkdir(parents=True, exist_ok=True)
    copied, _ = translate.prepare_backend(PINNED, build)
    executable = copied / '_build/default/p4spec/al_to_coq/main.exe'
    result = subprocess.run(['bash', str(ROOT / 'environment/env.sh'), 'frontend',
                             'dune', 'build', '--root', str(copied), '-j', '2',
                             'p4spec/al_to_coq/main.exe'],
                            capture_output=True, text=True, timeout=240)
    (build / 'build.log').write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(f'property backend build failed: {build / "build.log"}\n'
                           + (result.stdout + result.stderr)[-6000:])
    pointer.write_text(str(executable) + '\n')
    return executable


def _hash(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _translator_hash(directory=None):
    directory = ROOT / 'translator/src' if directory is None else directory
    return hashlib.sha256(b''.join((directory / path.name).read_bytes()
        for path in sorted((ROOT / 'translator/src').glob('*.ml')))).hexdigest()


def _snapshot_generation(run, source, config=None):
    """Both passes read the same private source bytes throughout compilation."""
    source = Path(source).resolve()
    captured = run / 'source' / source.name
    captured.parent.mkdir()
    captured.write_bytes(source.read_bytes())
    executable = build_backend()
    inputs = {'source': str(source), 'source_sha256': _hash(captured),
              'snapshot': str(captured),
              'translator_sha256': _translator_hash(executable.parent)}
    if config is not None:
        config = Path(config).resolve()
        copied_config = run / 'Property.toml'
        copied_config.write_bytes(config.read_bytes())
        inputs.update(config=str(config), config_sha256=_hash(copied_config))
    (run / 'generation-inputs.json').write_text(json.dumps(inputs, indent=2) + '\n')
    return captured, executable


def _validate_generation(run, source):
    captured = json.loads((run / 'generation-inputs.json').read_text())
    if str(Path(source).resolve()) != captured['source'] or _hash(source) != captured['source_sha256']:
        raise ValueError('source changed during property translation')
    if 'config' in captured and _hash(captured['config']) != captured['config_sha256']:
        raise ValueError('configuration changed during property translation')
    if _translator_hash() != captured['translator_sha256']:
        raise ValueError('translator changed during property translation')
    backend = json.loads((run / 'backend.json').read_text())
    if [item['sha256'] for item in backend['inputs']] != [captured['source_sha256']]:
        raise ValueError('backend source mismatch')
    return captured


def publication_plan(publication, source=None, config=None):
    publication = Path(publication)
    evidence = json.loads((publication / 'PassEvidence.json').read_text())
    if source is not None and _hash(source) != evidence['source_sha256']:
        raise ValueError('publication source mismatch')
    if config is not None and _hash(config) != evidence.get('config_sha256'):
        raise ValueError('publication configuration mismatch')
    if _translator_hash() != evidence['translator_sha256']:
        raise ValueError('translator changed since publication')
    plan_path = evidence['property_plan']
    entry = next((item for item in evidence['artifacts'] if item['path'] == plan_path), None)
    path = (publication / plan_path).resolve()
    if not path.is_relative_to(publication.resolve()) or entry is None or _hash(path) != entry['sha256']:
        raise ValueError('publication plan artifact changed')
    plan = json.loads(path.read_text())
    if config is not None and plan['precondition'] != tomllib.loads(Path(config).read_text())['precondition']:
        raise ValueError('publication precondition mismatch')
    return plan


def _generate_property(source, config, *, inventory=False, profile='fixture'):
    from .compiler import compile_spec
    run = Path(tempfile.mkdtemp(prefix='property-translation-', dir=STATE / 'checks'))
    snapshot, executable = _snapshot_generation(run, source, config)
    model = compile_spec(snapshot, run / 'Property.toml')
    output = run / 'spec'
    command = ['bash', str(ROOT / 'environment/env.sh'), 'frontend',
               str(executable), '--profile', profile, '--input', str(snapshot),
               '--property-pre', model.precondition, '--output', str(output),
               '--manifest', str(run / 'backend.json')]
    if inventory:
        command.append('--inventory')
    result = subprocess.run(command, capture_output=True, text=True, timeout=120)
    (run / 'generation.log').write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(f'property translation failed: {run / "generation.log"}\n'
                           + result.stderr)
    _validate_generation(run, source)
    return run, output


def translate_property(source, config, destination, *, profile='fixture'):
    """Publish checked property relations without changing the source specification."""
    destination = Path(destination).resolve()
    if not destination.is_relative_to(ROOT):
        raise ValueError('property publication must be inside this worktree')
    run, output = _generate_property(source, config, profile=profile)
    translate.compile_generated(output, profile, run, {'commands': []})
    _publish(source, destination, profile, run, output)
    # The compilation directory remains ignored evidence; callers can use it
    # for further proofs without creating .vo files beside published sources.
    (destination / '.runs' / run.name / 'Compilation.json').write_text(json.dumps({
        'run': str(run), 'spec': str(output), 'support': str(run / 'support')}) + '\n')
    return destination


def render_original(source, config, *, publication=None):
    from .coq_codec import render_input_codec, render_type_generators
    if publication is None:
        _, output = _generate_property(source, config, inventory=True)
        plan = json.loads((output / 'PropertyPlan.json').read_text())
    else:
        plan = publication_plan(publication, source, config)
    fields = [{**field, 'coq_projection': 'input_' + field['coq_name']}
              for field in plan['inputs']]
    record = '; '.join(f"{field['coq_projection']} : {field['coq_type']}" for field in fields)
    text = ('From QuickChick Require Import QuickChick.\n'
            'From Coq Require Import String Ascii ZArith.\n'
            'From ALCoq Require Import Execution.\n'
            f"From {plan['namespace']}.Generated Require Import Types_0000 InductiveRelations.\n"
            'Import QcDefaultNotation.\nOpen Scope string_scope.\n\n'
            + render_type_generators(plan['type_schema']) +
            f'Record Input := mkInput {{ {record} }}.\n'
            '#[global] Instance showInput : Show Input :=\n'
            '  {| show := fun _ => "Input" |}.\n\n'
            'Inductive predicate : Input -> Prop :=\n| precondition : ')
    bindings = [f"({v['coq_name']} : {v['coq_type']})" for v in plan['variables']]
    states = [f'property_state_{i}' for i in range(len(plan['calls']))]
    bindings += [f'({state} : State)' for state in states]
    if bindings:
        text += 'forall ' + ' '.join(bindings) + ',\n'
    for index, call in enumerate(plan['calls']):
        state = '{| next_fresh := 0 |}' if index == 0 else states[index - 1]
        values = call['outputs']
        result = ('tt' if not values else values[0] if len(values) == 1 else
                  '(' + ', '.join(values) + ')')
        args = ' '.join(call['inputs'])
        text += f"    {call['relation']} {args} {state} (Success {result}) {states[index]} ->\n"
    text += '    predicate (mkInput ' + ' '.join(f['coq_name'] for f in fields) + ').\n\n'
    return text + render_input_codec(fields, plan['type_schema'])


def _publish(source, destination, profile, run, generated):
    """Keep published semantics fixed and retain both pass outputs and their hashes."""
    source, destination = Path(source).resolve(), Path(destination).resolve()
    captured = _validate_generation(run, source)
    al = subprocess.run(
        ['bash', str(ROOT / 'environment/env.sh'), 'frontend',
         str(build_bridge()), 'dump', captured['snapshot']],
        capture_output=True, text=True, timeout=120)
    (run / 'frontend-al.txt').write_text(al.stdout)
    (run / 'frontend-al.log').write_text(al.stderr)
    if al.returncode:
        raise RuntimeError(f'frontend AL pass failed: {run / "frontend-al.log"}')
    _validate_generation(run, source)
    files = sorted(generated.rglob('*.v'))
    for path in files:
        target = destination / path.relative_to(generated)
        if target.exists() and target.read_bytes() != path.read_bytes():
            raise ValueError(f'fixed publication differs: {target}')
    archived = run / 'previous-publication'
    def copy(path, relative):
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists() and target.read_bytes() != path.read_bytes():
            archive = archived / relative
            archive.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(target, archive)
        shutil.copy2(path, target)
        return {'path': str(relative), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
    published = [copy(path, path.relative_to(generated)) for path in files]
    evidence_dir = Path('.runs') / run.name
    artifacts = [copy(run / name, evidence_dir / name) for name in ['frontend-al.txt', 'backend.json']]
    if (generated / 'PropertyPlan.json').exists():
        artifacts.append(copy(generated / 'PropertyPlan.json', evidence_dir / 'PropertyPlan.json'))
    namespace = ('Candidate' + profile[10:].capitalize() + 'Spec'
                 if profile.startswith('candidate_v') else
                 {'p4': 'P4Spec', 'wasm': 'WasmSpec', 'candidate': 'CandidateSpec'}.get(profile, 'FixtureSpec'))
    evidence = {
        'namespace': namespace, 'source': os.path.relpath(source, destination),
        'source_sha256': captured['source_sha256'],
        'frontend_al_sha256': hashlib.sha256((run / 'frontend-al.txt').read_bytes()).hexdigest(),
        'backend_manifest_sha256': hashlib.sha256((run / 'backend.json').read_bytes()).hexdigest(),
        'translator_sha256': captured['translator_sha256'],
        'evidence_dir': str(evidence_dir),
        'profile': profile, 'generated': published, 'artifacts': artifacts,
    }
    if 'config_sha256' in captured:
        evidence['config_sha256'] = captured['config_sha256']
    if (generated / 'PropertyPlan.json').is_file():
        evidence['property_plan'] = str(evidence_dir / 'PropertyPlan.json')
    (run / 'PassEvidence.json').write_text(json.dumps(evidence, indent=2) + '\n')
    copy(run / 'PassEvidence.json', Path('PassEvidence.json'))
    (run / 'publication.json').write_text(json.dumps({
        'destination': str(destination), 'source': str(source), 'pass_evidence': evidence},
        indent=2) + '\n')


def publish_demo(source=None, destination=None, profile='fixture'):
    source = Path(source or ROOT / 'specification/property_replay_demo/source/Property.watsup').resolve()
    destination = Path(destination or ROOT / 'specification/property_replay_demo').resolve()
    if not destination.is_relative_to(ROOT):
        raise ValueError('publication destination must be inside this worktree')
    run = Path(tempfile.mkdtemp(prefix='property-rocq.', dir=STATE / 'checks'))
    snapshot, executable = _snapshot_generation(run, source)
    generated = run / 'generated'
    result = subprocess.run(
        ['bash', str(ROOT / 'environment/env.sh'), 'frontend', str(executable),
         '--profile', profile, '--input', str(snapshot), '--output', str(generated),
         '--manifest', str(run / 'backend.json')],
        capture_output=True, text=True, timeout=120)
    (run / 'generation.log').write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(f'Coq generation failed: {run / "generation.log"}')
    translate.compile_generated(generated, profile, run, {'commands': []})
    _publish(source, destination, profile, run, generated)
    return run


def publish_candidate_helper():
    return publish_demo(
        ROOT / 'properties/property_replay_demo/candidates/v002/Helper.watsup',
        ROOT / 'specification/property_replay_demo/candidates/v002',
        profile='candidate')


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--candidate-helper', action='store_true')
    args = parser.parse_args()
    print(publish_candidate_helper() if args.candidate_helper else publish_demo())
