"""The two passes consume the same Input in separate evidence runs."""
from pathlib import Path
from argparse import Namespace
from contextlib import contextmanager
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from scripts.property import legacy as cli
from scripts.property.legacy import fixed_hashes, read_inputs


ROOT = Path(__file__).resolve().parents[2]
DEMO = ROOT / 'properties/property_replay_demo'
INPUT = json.dumps({'x': {'type': 'nat', 'value': '7'}})


class FixedOriginalTests(unittest.TestCase):
    @contextmanager
    def workspace(self):
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            root = Path(temp)
            prop = root / 'properties/property_replay_demo'
            prop.mkdir(parents=True)
            for name in ('Property.spectec', 'Property.toml', 'Original.v'):
                shutil.copy2(DEMO / name, prop / name)
            shutil.copytree(ROOT / 'specification/property_replay_demo',
                            root / 'specification/property_replay_demo',
                            ignore=shutil.ignore_patterns('candidates'))
            bridge = root / 'scripts/property/native'
            bridge.mkdir(parents=True)
            tool = root / 'scripts/property/tool.py'
            tool.parent.mkdir(parents=True, exist_ok=True)
            tool.write_text('# initial tool\n')
            with patch.object(cli, 'ROOT', root), patch.object(cli, 'BRIDGE', bridge):
                yield root, prop, tool

    def invoke(self, prop, action='prepare', *, samples_file=None, target='spec'):
        args = Namespace(property=prop, action=action, target=target, timeout=5,
                         input_json=None if samples_file else INPUT,
                         samples_file=samples_file)
        path, ok = cli.execute(args)
        return json.loads(path.read_text()), ok

    def saved_samples(self, prop):
        directory = prop / '.runs/saved-inputs'
        directory.mkdir()
        samples = directory / 'samples.json'
        samples.write_text('[' + INPUT + ']\n')
        (directory / 'batch.json').write_text(json.dumps({
            'fixed_hashes': cli.fixed_hashes(prop),
            'samples_sha256': cli.file_hash(samples)}) + '\n')
        return samples

    def test_later_direct_inputs_reject_each_fixed_semantic_source_change(self):
        changes = (
            'properties/property_replay_demo/Property.spectec',
            'properties/property_replay_demo/Property.toml',
            'properties/property_replay_demo/Original.v',
            'specification/property_replay_demo/source/Property.watsup',
            'specification/property_replay_demo/Generated/InductiveRelations_0000.v',
        )
        for relative in changes:
            with self.subTest(source=relative), self.workspace() as (root, prop, _):
                prepared, ok = self.invoke(prop)
                self.assertTrue(ok, prepared)
                baseline = prop / '.runs/fixed-original.json'
                self.assertTrue(baseline.is_file())
                before = baseline.read_bytes()
                source = root / relative
                source.write_text(source.read_text() + '\n')
                report, ok = self.invoke(prop, 'debug')
                self.assertFalse(ok, report)
                self.assertIn('fixed original changed', report['error'])
                self.assertIn(relative, report['error'])
                self.assertEqual(baseline.read_bytes(), before)

    def test_first_direct_debug_establishes_original_baseline(self):
        with self.workspace() as (_, prop, _):
            report, ok = self.invoke(prop, 'debug')
            self.assertTrue(ok, report)
            self.assertEqual(report['status_counts'], {'passed': 1})
            self.assertTrue((prop / '.runs/fixed-original.json').is_file())

    def test_tool_update_invalidates_batch_but_allows_new_direct_debug(self):
        with self.workspace() as (_, prop, tool):
            report, ok = self.invoke(prop)
            self.assertTrue(ok, report)
            samples = self.saved_samples(prop)
            tool.write_text('# updated tool\n')
            report, ok = self.invoke(prop, 'debug')
            self.assertTrue(ok, report)
            report, ok = self.invoke(prop, 'debug', samples_file=samples)
            self.assertFalse(ok, report)
            self.assertIn('fixed source changed since sampling', report['error'])

    def test_published_pass_artifact_update_invalidates_batch(self):
        for name in ('frontend-al.txt', 'backend.json'):
            with self.subTest(artifact=name), self.workspace() as (root, prop, _):
                published = root / 'specification/property_replay_demo/Generated'
                artifact = published / name
                artifact.write_text('initial artifact\n')
                (published / 'PassEvidence.json').write_text(json.dumps({
                    'artifacts': [{'path': name}]}) + '\n')
                report, ok = self.invoke(prop)
                self.assertTrue(ok, report)
                samples = self.saved_samples(prop)
                artifact.write_text('changed artifact\n')
                report, ok = self.invoke(prop, 'debug', samples_file=samples)
                self.assertFalse(ok, report)
                self.assertIn('fixed source changed since sampling', report['error'])

    def test_new_candidate_helper_does_not_change_fixed_original(self):
        with self.workspace() as (root, prop, _):
            report, ok = self.invoke(prop)
            self.assertTrue(ok, report)
            baseline = prop / '.runs/fixed-original.json'
            self.assertTrue(baseline.is_file())
            before = baseline.read_bytes()
            candidate = prop / 'candidates/v003'
            candidate.mkdir(parents=True)
            (candidate / 'Helper.watsup').write_text('// candidate helper\n')
            generated = root / 'specification/property_replay_demo/candidates/v003'
            generated.mkdir(parents=True)
            (generated / 'Spec.v').write_text('Definition candidate_only := 3.\n')
            report, ok = self.invoke(prop, 'debug')
            self.assertTrue(ok, report)
            self.assertEqual(baseline.read_bytes(), before)

    def test_debug_batch_survives_adapter_change_and_removal(self):
        with self.workspace() as (root, prop, _):
            adapter = root / 'adapters/property_replay_demo/demo_external.py'
            adapter.parent.mkdir(parents=True)
            adapter.write_text('raise RuntimeError("must not run")\n')
            report, ok = self.invoke(prop)
            self.assertTrue(ok, report)
            samples = self.saved_samples(prop)
            adapter.write_text('raise RuntimeError("changed")\n')
            for remove in (False, True):
                if remove:
                    adapter.unlink()
                report, ok = self.invoke(prop, 'debug', samples_file=samples)
                self.assertTrue(ok, report)
                self.assertEqual(report['external_calls'], 0)
                self.assertEqual(report['status_counts'], {'passed': 1})

    def test_failed_prepare_preserves_structured_analysis_evidence(self):
        with self.workspace() as (_, prop, _):
            config = prop / 'Property.toml'
            config.write_text(config.read_text().replace(
                'observed_outputs = [0]', 'observed_outputs = []'))
            report, ok = self.invoke(prop, target='replay')
            self.assertFalse(ok, report)
            self.assertIn('consumer B', report['error'])
            evidence = report.get('analysis_failure')
            self.assertIsInstance(evidence, dict)
            self.assertEqual(evidence['helper_path'], ['Pre'])
            self.assertEqual(evidence['premise']['kind'], 'B')


class WorkflowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        (DEMO / '.runs').mkdir(exist_ok=True)

    def invoke(self, *args):
        result = subprocess.run([sys.executable, '-B', '-m', 'scripts.property.cli',
                                 str(DEMO), *args], cwd=ROOT,
                                capture_output=True, text=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        path = Path(result.stdout.strip())
        return json.loads(path.read_text()), path.parent

    def test_prepare_replay_and_debug_are_separate(self):
        prepared, _ = self.invoke('prepare', '--target', 'replay')
        self.assertEqual(prepared['status'], 'passed')
        replay, replay_dir = self.invoke('replay', '--input-json', INPUT)
        debug, debug_dir = self.invoke('debug', '--input-json', INPUT)
        self.assertEqual(replay['status_counts'], {'failed': 1})
        self.assertEqual(debug['status_counts'], {'passed': 1})
        self.assertEqual(replay['external_calls'], 1)
        self.assertEqual(debug['external_calls'], 0)
        self.assertIn('adapter_hashes', replay)
        self.assertNotIn('adapter_hashes', debug)
        self.assertNotEqual(replay_dir, debug_dir)

    def test_old_batch_is_rejected_when_fixed_hash_differs(self):
        with tempfile.TemporaryDirectory(dir=DEMO / '.runs') as temp:
            run = Path(temp)
            samples = run / 'samples.json'
            samples.write_text('[null]\n')
            (run / 'batch.json').write_text(json.dumps({
                'fixed_hashes': {}, 'samples_sha256': 'wrong'}) + '\n')
            class Args:
                input_json = None
                samples_file = samples
            with self.assertRaisesRegex(ValueError, 'fixed source changed'):
                read_inputs(Args(), DEMO, fixed_hashes(DEMO))


if __name__ == '__main__':
    unittest.main()
