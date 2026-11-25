"""A single declaration uses shared setup through real Coq and native AL."""
from argparse import Namespace
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.property.context import candidate_hashes
from scripts.property.prepare import prepare_property


ROOT = Path(__file__).resolve().parents[2]
INPUT = {'x': {'type': 'nat', 'value': '7'}}
SPEC = '''var x : nat
var b : nat
var c : nat
var u : nat
relation External: nat nat nat hint(input %0)
rule External/main: x b u
  -- if b = 10
  -- if u = 99
relation B: nat nat hint(input %0)
rule B/main: b c
  -- if c = $(b + 1)
relation UnusedInner: nat nat hint(input %0)
rule UnusedInner/main: x b
  -- if b = 0
relation UnusedOuter: nat nat hint(input %0)
rule UnusedOuter/main: x b
  -- UnusedInner: x b
relation Test: nat nat hint(input %0 %1)
rule Test/main: x b
  -- if x = b
'''
DECLARATION = '''property [external_result]:
  (x : nat)
  c = $(x + 4)
  -- External: x b u
  -- B: b c
'''


class UnifiedWorkflowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(
            prefix='unified-workflow-', dir=ROOT / '_opam-testing-theorems/checks')
        cls.directory = Path(cls.temporary.name)
        cls.specification = cls.directory / 'specification'
        cls.specification.mkdir()
        (cls.specification / 'Spec.watsup').write_text(SPEC)
        cls.manifest = cls.specification / 'Specification.toml'
        cls.manifest.write_text('id="demo"\nsources=["Spec.watsup"]\nprofile="fixture"\n')
        cls.prop = cls.directory / 'property_one'
        cls.prop.mkdir()
        (cls.prop / 'Property.spectec').write_text(DECLARATION)
        cls.adapters = []
        for value in (10, 20):
            directory = cls.directory / ('adapter_' + str(value))
            directory.mkdir()
            (directory / 'run.py').write_text(
                'import json,sys\nfor line in sys.stdin:\n'
                ' r=json.loads(line)\n'
                ' print(json.dumps({"status":"returned","fresh_id":r["fresh_id"],'
                '"outputs":[{"position":0,"value":{"type":"nat","value":"' +
                str(value) + '"}}]}),flush=True)\n')
            manifest = directory / 'Adapter.toml'
            manifest.write_text('specification="demo"\n[[external]]\nrelation="External"\n'
                                'adapter="external"\ncommand=["python3","run.py"]\n'
                                'conversion="json-v1"\nobserved_outputs=[0]\n')
            with manifest.open('a') as stream:
                for relation in ('UnusedInner', 'UnusedOuter'):
                    stream.write(f'[[external]]\nrelation="{relation}"\nadapter="external"\n'
                                 'command=["python3","run.py"]\nconversion="json-v1"\n'
                                 'observed_outputs=[0]\n')
            cls.adapters.append(manifest)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def module(self):
        self.assertIsNotNone(importlib.util.find_spec('scripts.property.commands'),
                             'unified declaration workflow is not implemented')
        from scripts.property import commands
        return commands

    def invoke(self, action, implementation=None, **options):
        args = Namespace(property=self.prop, action=action, spec=self.manifest,
                         implementation=implementation, target='spec', timeout=20,
                         candidate='v001', count=4, size=8, seed=7,
                         input_json=json.dumps(INPUT), samples_file=None)
        for key, value in options.items():
            setattr(args, key, value)
        path, ok = self.module().execute(args)
        report = json.loads(path.read_text())
        self.assertTrue(ok, report.get('error', report))
        return report

    def test_00_shared_specification_is_read_only_and_same_named_properties_are_independent(self):
        from scripts.check import Session
        before = {str(path.relative_to(self.specification)): path.read_bytes()
                  for path in self.specification.rglob('*') if path.is_file()}
        publications = []
        for group, offset in [('first', 4), ('second', 5)]:
            prop = self.directory / group / 'same_name'
            prop.mkdir(parents=True)
            (prop / 'Property.spectec').write_text(
                DECLARATION.replace('x + 4', f'x + {offset}'))
            prepared = prepare_property(prop, self.manifest)
            self.assertTrue(prepared.publication.is_relative_to(prop / '.runs'),
                            'property translation must be owned by its property')
            publications.append(prepared.publication)
            session = Session(prop)
            session.check()
            session.finish()
            self.assertEqual(session.report['status'], 'passed')
        self.assertNotEqual(*publications)
        after = {str(path.relative_to(self.specification)): path.read_bytes()
                 for path in self.specification.rglob('*') if path.is_file()}
        self.assertEqual(after, before, 'preparation must not write into shared specification')

    def test_01_prepare_check_derive_and_same_inputs_two_implementations(self):
        prepared = self.invoke('prepare')
        self.assertFalse((self.prop / 'Property.toml').exists())
        self.assertEqual(prepared['input_fields'], [{'name': 'x', 'type': 'nat'}])
        self.assertIn('Inductive predicate', (self.prop / 'Original.v').read_text())
        from scripts.property.rocq import publish_demo
        helper = self.prop / 'candidates/v001/Helper.watsup'
        helper.write_text('var n : nat\nrelation Helper: nat nat hint(input %0)\n'
                          'rule Helper/main: n n\n')
        helper_publication = Path(prepared['publication']) / 'candidates/v001'
        publish_demo(helper, helper_publication, profile='candidate')
        candidate = self.prop / 'candidates/v001/Candidate.v'
        candidate.write_text('From CandidateSpec.Generated Require Import InductiveRelations.\n'
                             + candidate.read_text())
        for script, extra in [('check.py', []), ('run.py', ['--candidate', 'v001', '--derive-only'])]:
            result = subprocess.run([sys.executable, '-B', str(ROOT / 'scripts' / script),
                                     str(self.prop), *extra], capture_output=True,
                                    text=True, timeout=240, cwd=ROOT)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        sampled = self.invoke('sample')
        self.assertGreater(sampled['generated'], 0)
        sample_path = Path(sampled['samples_file'])
        for adapter in self.adapters:
            report = self.invoke('replay', adapter, input_json=None, samples_file=sample_path)
            self.assertEqual(report['external_calls'], sampled['generated'])
            self.assertIn('implementation_hashes', report)
        actual = self.invoke('replay', self.adapters[1])
        expected = self.invoke('replay', self.adapters[0])
        self.assertEqual(actual['status_counts'], {'failed': 1})
        self.assertEqual(expected['status_counts'], {'passed': 1})
        result = json.loads(Path(actual['results_file']).read_text())[0]
        self.assertEqual(result['trace']['pre_outputs'][0]['value'], '21')
        self.assertTrue(any(str(self.prop / 'Property.spectec') in item['source']
                            for item in result['trace']['markers']))
        debug = self.invoke('debug', self.directory / 'missing-adapter.toml')
        self.assertEqual(debug['status_counts'], {'passed': 1})
        self.assertEqual(debug['external_calls'], 0)
        generated = helper_publication / 'Generated/InductiveRelations.v'
        before = generated.read_text()
        try:
            generated.write_text(before + '\n(* changed candidate publication *)\n')
            args = Namespace(property=self.prop, action='debug', spec=self.manifest,
                             implementation=None, samples_file=sample_path,
                             input_json=None, timeout=20)
            path, ok = self.module().execute(args)
            self.assertFalse(ok, 'a batch must reject a changed candidate publication')
            self.assertIn('candidate changed', json.loads(path.read_text())['error'])
        finally:
            generated.write_text(before)

    def test_03_second_property_reuses_setup_and_derives_non_relation_condition(self):
        second = self.directory / 'property_two'
        second.mkdir(exist_ok=True)
        source = DECLARATION.replace('[external_result]', '[only_seven]').replace(
            '  -- External:', '  -- if x = 7\n  -- External:')
        (second / 'Property.spectec').write_text(source)
        args = Namespace(property=second, action='sample', spec=self.manifest,
                         implementation=None, candidate='v001', count=8, size=16, seed=7)
        path, ok = self.module().execute(args)
        report = json.loads(path.read_text())
        self.assertTrue(ok, report.get('error', report))
        samples = json.loads(Path(report['samples_file']).read_text())
        self.assertTrue(any(sample is not None for sample in samples))
        self.assertTrue(all(sample is None or sample == INPUT for sample in samples))
        args.action = 'replay'
        args.implementation = self.adapters[1]
        args.samples_file = Path(report['samples_file'])
        args.input_json = None
        args.timeout = 20
        path, ok = self.module().execute(args)
        report = json.loads(path.read_text())
        self.assertTrue(ok, report.get('error', report))
        self.assertGreater(report['status_counts'].get('failed', 0), 0)

    def test_02_observation_failure_runs_no_adapter_and_semantic_change_rejected(self):
        self.invoke('prepare')
        bad = self.adapters[1].parent / 'Bad.toml'
        bad.write_text(self.adapters[1].read_text().replace('observed_outputs=[0]',
                                                         'observed_outputs=[]'))
        args = Namespace(property=self.prop, action='prepare', spec=self.manifest,
                         implementation=bad, target='replay', timeout=20)
        path, ok = self.module().execute(args)
        self.assertFalse(ok)
        report = json.loads(path.read_text())
        self.assertEqual(report['compile_error_code'], 'replay_observability_error')
        self.assertIn(str(self.prop / 'Property.spectec'), json.dumps(report['analysis_failure']))
        original = (self.prop / 'Original.v').read_bytes()
        source = self.prop / 'Property.spectec'
        before = source.read_text()
        try:
            source.write_text(before.replace('x + 4', 'x + 5'))
            result = subprocess.run([sys.executable, '-B', str(ROOT / 'scripts/check.py'),
                                     str(self.prop)], capture_output=True, text=True, timeout=30)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('changed', result.stderr)
            self.assertEqual((self.prop / 'Original.v').read_bytes(), original)
        finally:
            source.write_text(before)

    def test_04_preparation_error_uses_original_property_location(self):
        prop = self.directory / 'unsupported_property'
        prop.mkdir(exist_ok=True)
        source = prop / 'Property.spectec'
        source.write_text('property [negative]:\n  (x : nat)\n  true\n  -- External :/ x x x\n')
        args = Namespace(property=prop, action='prepare', target='spec',
                         spec=self.manifest, implementation=None)
        path, ok = self.module().execute(args)
        self.assertFalse(ok)
        report = json.loads(path.read_text())
        self.assertIn('elab/negated-premise-has-outputs', report['error'])
        self.assertIn(str(source) + ':4:', report['error'])
        self.assertNotIn('Property.lowered.watsup', report['error'])


    def test_05_preexisting_candidate_publication_is_separate_at_first_prepare(self):
        from scripts.property.rocq import publish_demo
        prop = self.directory / 'preexisting_candidate'
        prop.mkdir()
        (prop / 'Property.spectec').write_text(DECLARATION)
        helper = prop / 'Helper.watsup'
        helper.write_text('var n : nat\nrelation Helper: nat nat hint(input %0)\n'
                          'rule Helper/main: n n\n')
        publication = prop / '.runs/publication'
        selected = publication / 'candidates/v001'
        publish_demo(helper, selected, profile='candidate')
        prepared = prepare_property(prop, self.manifest)
        self.assertFalse(any(Path(path).is_relative_to(selected)
                             for path in prepared.context['semantic_hashes']))
        candidate_hashes(prop, 'v001')
        generated = selected / 'Generated/InductiveRelations.v'
        before = generated.read_text()
        generated.write_text(before + '\n(* candidate exploration *)\n')
        try:
            prepare_property(prop, self.manifest)
            with self.assertRaisesRegex(ValueError, 'Generated Coq changed'):
                candidate_hashes(prop, 'v001')
        finally:
            generated.write_text(before)


if __name__ == '__main__':
    unittest.main()
