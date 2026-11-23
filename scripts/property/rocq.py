"""Translate the fixed demo through the existing SpecTec to Coq backend."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import tempfile

from scripts import translate
from .bridge import ROOT, PINNED, build_bridge


STATE = ROOT / '_opam-testing-theorems'


def render_original(source, config):
    """Render the Input witness predicate from a direct-call Pre rule.

    The selected demo has a single nat Input and variable-only relation
    premises. Other premise forms require a translated temporary relation.
    """
    from .compiler import CompileError, compile_spec

    model = compile_spec(source, config)
    if len(model.inputs) != 1 or model.inputs[0]['type'] != 'nat':
        raise CompileError('property predicate renderer needs one nat Input')
    text = Path(source).read_text()
    variables = dict(re.findall(r'^var\s+(\w+)\s*:\s*(\w+)\s*$', text, re.M))
    block = re.search(r'^rule\s+' + re.escape(model.precondition) +
                      r'/\w+:\s*[^\n]*\n((?:\s+--[^\n]*\n)*)', text, re.M)
    if block is None:
        raise CompileError('Pre rule body is unavailable')
    definitions = {item['name']: item for item in model.definitions}
    calls = []
    witnesses = [model.inputs[0]['name']]
    for line in block.group(1).splitlines():
        call = re.fullmatch(r'\s*--\s*(\w+)\s*:\s*([\w\s]+)', line)
        if call is None:
            raise CompileError('non-call premise needs a translated temporary relation')
        name, args = call.group(1), call.group(2).split()
        definition = definitions.get(name)
        if definition is None or len(definition['output_types']) != 1 or \
                len(args) != len(definition['input_types']) + 1:
            raise CompileError(f'{name}: unsupported direct relation application')
        for arg in args:
            if arg not in variables:
                raise CompileError(f'{arg}: no declared witness type')
            if arg not in witnesses:
                witnesses.append(arg)
        calls.append((name, args, len(definition['input_types'])))
    if not calls:
        raise CompileError('Pre has no relation premise')
    if any(variables[name] != 'nat' for name in witnesses):
        raise CompileError('demo Coq renderer supports nat witnesses')
    states = ['middle', 'final'] if len(calls) == 2 else \
        [f'state_{i}' for i in range(1, len(calls) + 1)]
    premises = []
    for index, (name, args, count) in enumerate(calls):
        start = '{| next_fresh := 0 |}' if index == 0 else states[index - 1]
        prefix = f'    g_fixture_rel_{name}_execute ' + \
                 ' '.join(args[:count]) + f' {start}'
        if index == 0:
            premises.append(prefix + f'\n      (Success {args[count]}) {states[index]} ->')
        else:
            premises.append(prefix + f' (Success {args[count]}) {states[index]} ->')
    input_name = model.inputs[0]['name']
    return ('''From QuickChick Require Import QuickChick.
From Coq Require Import String.
From ALCoq Require Import Execution.
From FixtureSpec.Generated Require Import InductiveRelations_0000.
Import QcDefaultNotation.
Open Scope string_scope.

''' + f'Record Input := mkInput {{ input_{input_name} : nat }}.\n' +
'''#[global] Instance showInput : Show Input :=
''' + f'  {{| show := fun i => show (input_{input_name} i) |}}.\n' +
'''
(* Each premise applies the already translated relation.  The intermediate
   state is a constructor witness and is passed to the next premise. *)
Inductive predicate : Input -> Prop :=
''' + f'| precondition : forall ({" ".join(witnesses)} : nat) '
        f'({" ".join(states)} : State),\n' +
        '\n'.join(premises) + '\n' +
        f'    predicate (mkInput {input_name}).\n\n' +
        f'Definition encode_input (i : Input) : string :=\n'
        f'  "{{""{input_name}"":{{""type"":""nat"",""value"":""" ++\n'
        f'  show (input_{input_name} i) ++ """}}}}".\n')


def publish_demo(source=None, destination=None, profile='fixture'):
    source = Path(source or ROOT / 'specification/property_replay_demo/source/Property.watsup').resolve()
    destination = Path(destination or ROOT / 'specification/property_replay_demo').resolve()
    if not destination.is_relative_to(ROOT):
        raise ValueError('publication destination must be inside this worktree')
    run = Path(tempfile.mkdtemp(prefix='property-rocq.', dir=STATE / 'checks'))
    copied, _ = translate.prepare_backend(PINNED, run)
    build = subprocess.run(
        ['bash', str(ROOT / 'environment/env.sh'), 'frontend', 'dune',
         'build', '--root', str(copied), '-j', '2', 'p4spec/al_to_coq/main.exe'],
        capture_output=True, text=True, timeout=240)
    (run / 'backend-build.log').write_text(build.stdout + build.stderr)
    if build.returncode:
        raise RuntimeError(f'backend build failed: {run / "backend-build.log"}')
    generated = run / 'generated'
    command = ['bash', str(ROOT / 'environment/env.sh'), 'frontend',
               str(copied / '_build/default/p4spec/al_to_coq/main.exe'),
               '--profile', profile, '--input', str(source),
               '--output', str(generated), '--manifest', str(run / 'backend.json')]
    result = subprocess.run(command, capture_output=True, text=True, timeout=120)
    (run / 'generation.log').write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(f'Coq generation failed: {run / "generation.log"}')
    manifest = json.loads((run / 'backend.json').read_text())
    translate.compile_generated(generated, profile, run, {'commands': []})
    al = subprocess.run(
        ['bash', str(ROOT / 'environment/env.sh'), 'frontend',
         str(build_bridge()), 'dump', str(source)],
        capture_output=True, text=True, timeout=120)
    (run / 'frontend-al.txt').write_text(al.stdout)
    (run / 'frontend-al.log').write_text(al.stderr)
    if al.returncode:
        raise RuntimeError(f'frontend AL pass failed: {run / "frontend-al.log"}')
    files = sorted(generated.rglob('*.v'))
    archived = run / 'previous-publication'
    copied_files = []
    for path in files:
        relative = path.relative_to(generated)
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists() and target.read_bytes() != path.read_bytes():
            archive = archived / relative
            archive.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(target, archive)
        shutil.copy2(path, target)
        copied_files.append({'path': str(relative),
                             'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
    translator_sources = sorted((ROOT / 'translator/src').glob('*.ml'))
    translator_digest = hashlib.sha256(
        b''.join(path.read_bytes() for path in translator_sources)).hexdigest()
    pass_evidence = {
        'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'frontend_al_sha256': hashlib.sha256(al.stdout.encode()).hexdigest(),
        'backend_manifest_sha256': hashlib.sha256((run / 'backend.json').read_bytes()).hexdigest(),
        'translator_sha256': translator_digest,
        'profile': profile,
        'generated': copied_files,
    }
    evidence_path = destination / 'PassEvidence.json'
    if evidence_path.exists() and evidence_path.read_text() != json.dumps(pass_evidence, indent=2) + '\n':
        archived.mkdir(parents=True, exist_ok=True)
        shutil.copy2(evidence_path, archived / 'PassEvidence.json')
    evidence_path.write_text(json.dumps(pass_evidence, indent=2) + '\n')
    report = {'source': str(source),
              'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
              'pinned_frontend': str(PINNED),
              'backend_manifest': manifest,
              'published': copied_files,
              'pass_evidence': pass_evidence}
    (run / 'publication.json').write_text(json.dumps(report, indent=2) + '\n')
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
