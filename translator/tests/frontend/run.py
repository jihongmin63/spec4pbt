#!/usr/bin/env python3
"""Exercise actual Pass.algo fixture inventory using an already-built backend."""
import argparse
import json
from pathlib import Path
import subprocess


def check(backend, run_dir):
    run_dir = Path(run_dir)
    run_dir.mkdir(parents=True, exist_ok=True)
    fixture = Path(__file__).with_name('inventory.watsup')
    command = [str(backend), '--profile', 'fixture', '--input', str(fixture), '--output', str(run_dir), '--manifest', str(run_dir / 'manifest.json')]
    completed = subprocess.run(command + ['--inventory'], capture_output=True, text=True)
    (run_dir / 'frontend.log').write_text(completed.stdout + completed.stderr)
    if completed.returncode:
        raise AssertionError(completed.stderr)
    (run_dir / 'inventory-manifest.json').write_text((run_dir / 'manifest.json').read_text())
    inventory = json.loads((run_dir / 'inventory.json').read_text())
    decls = {d['source_name']: d for d in inventory['declarations']}
    assert decls['Noncontiguous']['signature']['input_positions'] == [0, 2]
    assert decls['Noncontiguous']['signature']['output_positions'] == [1, 3]
    assert decls['Conditional']['signature']['output_shape'] == 'unit-no-outputs'
    assert decls['SingleTuple']['signature']['output_shape'] == 'single'
    assert decls["a'"]['generated_name'] != decls['a_x27_']['generated_name']
    assert decls['n']['disposition'] == 'consumed-metadata'
    assert decls['empty']['kind'] == 'FuncDecD'
    assert decls['uninhabited']['kind'] == 'TypD'
    assert decls['uninhabitedPoly']['kind'] == 'TypD'
    assert inventory['raw_al_declaration_count'] + 2 == inventory['declaration_count']
    recovered = {n['source_name']: n for n in inventory['normalizations']}
    assert recovered['uninhabited']['representation'] == 'TypD(VariantT[])'
    assert recovered['uninhabitedPoly']['type_parameters'] == ['T']
    assert decls['callback']['signature']['type_parameters'] == ['T']
    assert all(d['location']['left']['line'] > 0 for d in inventory['declarations'])
    assert inventory['translation_complete'] is False
    callback = next(c for c in inventory['callback_schemas'] if c['owner'] == 'callback')
    assert callback['kind'] == 'DefP'
    assert callback['free_type_parameters'] == ['T']
    assert callback['bound_type_parameters'] == []
    again = subprocess.run(command + ['--inventory'], capture_output=True, text=True)
    assert again.returncode == 0
    assert json.loads((run_dir / 'inventory.json').read_text()) == inventory
    # Inventory and complete translation have distinct recorded stages.
    completed = subprocess.run(command, capture_output=True, text=True)
    assert completed.returncode == 0, completed.stderr
    assert (run_dir / 'Generated/InductiveRelations.v').is_file()
    assert not list((run_dir / 'Generated').glob('Bodies_*.v'))
    assert not (run_dir / 'Generated/Program.v').exists()
    assert json.loads((run_dir / 'manifest.json').read_text())['status'] == 'coq-generated'
    (run_dir / 'translation-manifest.json').write_text((run_dir / 'manifest.json').read_text())
    (run_dir / 'translation.log').write_text(completed.stdout + completed.stderr)
    invalid = run_dir / 'invalid.watsup'
    invalid.write_text('syntax ! invalid\n')
    command[command.index(str(fixture))] = str(invalid)
    completed = subprocess.run(command + ['--inventory'], capture_output=True, text=True)
    assert completed.returncode != 0
    diagnostic = json.loads((run_dir / 'manifest.json').read_text())['diagnostics'][0]
    assert diagnostic['location']['left']['file'] == str(invalid)
    assert diagnostic['reason']
    (run_dir / 'invalid-manifest.json').write_text((run_dir / 'manifest.json').read_text())
    (run_dir / 'invalid.log').write_text(completed.stdout + completed.stderr)
    (run_dir / 'report.json').write_text(json.dumps({'suite': 'frontend-fixture', 'status': 'passed', 'backend': str(backend), 'assertions': ['input-output-positions', 'callbacks', 'metadata', 'injective-names', 'source-locations', 'determinism', 'translation-fail-closed', 'frontend-diagnostics']}, indent=2) + '\n')
    print('Frontend fixture: inventory/signatures/metadata/names/locations/fail-closed diagnostics passed')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--backend', type=Path, required=True)
    parser.add_argument('--run-dir', type=Path, required=True)
    args = parser.parse_args()
    check(args.backend, args.run_dir)
