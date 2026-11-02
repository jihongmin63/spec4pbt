"""Sampler scratch ownership must not outlive a call or invalidate an active run."""
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from scripts.property.clause import CertifiedProperty
from scripts.property import runner
from scripts.toolchain import SCRATCH_DIRECTORY, digest


class SamplerCleanupTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.scratch = self.root / SCRATCH_DIRECTORY
        self.dependency = self.root / 'generator-dependency.olean'
        self.dependency.write_bytes(b'certified dependency fixture')
        self.samples = [{'index': 0, 'input': {'n': 3}}, {'index': 1, 'input': {'n': 4}}]
        self.driver = None
        self.bundle = CertifiedProperty(
            project=self.root, directory=self.root, namespace='Fixture.Contract', module='Fixture.Contract',
            executable=self.root / 'unused-native', spec_paths=(), property_path=self.root / 'property.watsup',
            property_name='positive', toolchain={}, fingerprints={},
            generator_module='Fixture.Generator', generator='Fixture.generator',
            plan={'plan_id': 'cleanup-fixture', 'calls': [
                {'id': 'goal', 'relation': 'Copy', 'profile_selectors': []}]})
        (self.root / 'certificate.json').write_text('{}\n')
        metadata = {'schema_version': 1, 'observations': [
            {'id': 'copy', 'relation': 'Copy', 'observe': []}]}
        for filename in ('metadata-config.json', 'catalog-config.json'):
            (self.root / filename).write_text(json.dumps(metadata))
        for filename in ('manifest.json', 'catalog-manifest.json'):
            (self.root / filename).write_text(json.dumps({'relations': {'Copy': {}}}))
        self.adapter = self.root / 'adapter.py'
        self.adapter.write_text('''import json, sys
request = json.load(sys.stdin)
reply = {key: request[key] for key in ('plan_id', 'case_id', 'occurrence_id', 'relation_id')}
reply.update(status='success', observation={})
print(json.dumps(reply))
''')
        self.implementation = self.root / 'implementation.toml'
        self.implementation.write_text(
            'schema_version = 1\nid = "cleanup-fixture"\n[[executions]]\nrelation = "Copy"\nadapter = '
            + json.dumps([sys.executable, str(self.adapter)]) + '\n')
        self.output = self.root / 'results'
        self.enterContext(patch('scripts.property.clause.resolve_toolchain',
                                return_value=SimpleNamespace(identity=lambda: {})))
        self.enterContext(patch.object(CertifiedProperty, 'invoke', side_effect=self.native))
        self.enterContext(patch.object(runner, 'fingerprint_dependencies', self.fingerprint))
        self.enterContext(patch.object(runner, 'run_checked', self.sample_output))

    def fingerprint(self, project, roots, timeout):
        self.driver, = roots
        return {str(path): digest(path) for path in (self.driver, self.dependency)}

    def sample_output(self, command, project, timeout):
        self.assertEqual(Path(command[-1]), self.driver)
        self.assertTrue(self.driver.is_file())
        return '\n'.join(json.dumps(sample) for sample in self.samples)

    def native(self, mode, input_value, trace, index=None, timeout_seconds=60):
        # This is the native executable boundary; the runner, adapter and files are real.
        self.assertTrue(self.driver.is_file(), 'driver must survive every external case')
        if mode == 'request':
            return {'ready': True, 'input': [input_value['n']]}
        if mode == 'validate':
            return {'valid': True}
        if mode == 'check':
            return {'verdict': 'pass'}
        self.fail('unexpected native operation: ' + mode)

    def sample(self):
        return runner.sample_inputs(self.bundle, count=2, size=4, seed=0, timeout_seconds=10)

    def run_property(self):
        return runner.run_property(self.bundle, implementation=self.implementation, output=self.output,
                                   count=2, size=4, seed=0, timeout_seconds=10)

    def assert_clean(self):
        self.assertEqual(list(self.scratch.glob('sampler-*')), [])
        self.assertTrue(self.dependency.is_file())

    def test_standalone_samples_are_returned_without_leaving_scratch(self):
        samples, fingerprints = self.sample()
        self.assertEqual(samples, self.samples)
        self.assertIn(str(self.dependency), fingerprints)
        self.assert_clean()

    def test_sampling_errors_remove_scratch(self):
        failures = [
            ('dependency discovery', 'fingerprint_dependencies', ValueError('dependency discovery failed')),
            ('compiler', 'run_checked', ChildProcessError('compiler failed')),
            ('timeout', 'run_checked', TimeoutError('sampler timed out')),
            ('invalid JSON', 'run_checked', 'not JSON'),
            ('wrong count', 'run_checked', ''),
            ('wrong index', 'run_checked', '{"index":2,"input":{}}\n{"index":1,"input":{}}'),
        ]
        for label, target, failure in failures:
            with self.subTest(label=label):
                options = {'side_effect': failure} if isinstance(failure, Exception) else {'return_value': failure}
                with patch.object(runner, target, **options):
                    with self.assertRaises((ValueError, ChildProcessError, TimeoutError)):
                        self.sample()
                self.assert_clean()

    def test_run_retains_driver_through_cases_and_preserves_results_after_cleanup(self):
        result = self.run_property()
        self.assertEqual((result.status, result.completed), ('passed', 2))
        self.assert_clean()
        self.assertEqual(json.loads((self.output / 'samples.json').read_text()), self.samples)
        record = json.loads((self.output / 'run.json').read_text())
        self.assertIn(str(self.driver), record['sampler_dependencies'])
        for name in ('case-000000', 'case-000001'):
            self.assertEqual(json.loads((self.output / name / 'result.json').read_text())['verdict'], 'pass')
            self.assertTrue((self.output / name / 'trace.json').is_file())
        self.assertEqual(json.loads((self.output / 'result.json').read_text())['status'], 'passed')

    def test_adapter_error_preserves_evidence_and_removes_scratch(self):
        self.adapter.write_text('raise SystemExit("adapter failed")\n')
        original_native = self.native

        def native(mode, *args, **kwargs):
            if mode == 'check':
                return {'verdict': 'error', 'reason': 'adapter_error'}
            return original_native(mode, *args, **kwargs)

        with patch.object(CertifiedProperty, 'invoke', side_effect=native):
            result = self.run_property()
        self.assertEqual((result.status, result.completed), ('error', 1))
        self.assert_clean()
        case = self.output / 'case-000000'
        trace = json.loads((case / 'trace.json').read_text())
        self.assertEqual(trace['entries'][0]['status'], 'execution_error')
        self.assertTrue((case / 'call-000' / 'process.json').is_file())
        self.assertTrue((self.output / 'result.json').is_file())

    def test_run_write_error_removes_scratch_without_deleting_saved_evidence(self):
        write_json = runner.write_json

        def fail_summary(path, value):
            if path == self.output / 'result.json':
                raise OSError('result write failed')
            write_json(path, value)

        with patch.object(runner, 'write_json', fail_summary):
            with self.assertRaisesRegex(OSError, 'result write failed'):
                self.run_property()
        self.assert_clean()
        self.assertTrue((self.output / 'samples.json').is_file())
        self.assertTrue((self.output / 'case-000001' / 'trace.json').is_file())

    def test_mutation_during_sampling_is_rejected_and_cleans_scratch(self):
        original_output = self.sample_output

        def mutate(command, project, timeout):
            result = original_output(command, project, timeout)
            self.driver.write_text('changed sampler')
            return result

        with patch.object(runner, 'run_checked', mutate):
            with self.assertRaisesRegex(ValueError, 'certified sampler is stale'):
                self.sample()
        self.assert_clean()

    def test_driver_and_dependency_changes_between_cases_are_rejected_and_cleaned(self):
        for changed in ('driver', 'dependency'):
            with self.subTest(changed=changed):
                self.output = self.root / ('results-' + changed)
                original_native = self.native

                def mutate(mode, *args, **kwargs):
                    result = original_native(mode, *args, **kwargs)
                    if mode == 'check':
                        getattr(self, changed).write_text('changed during first case')
                    return result

                with patch.object(CertifiedProperty, 'invoke', side_effect=mutate):
                    with self.assertRaisesRegex(ValueError, 'certified sampler is stale'):
                        self.run_property()
                self.assert_clean()
                self.assertTrue((self.output / 'case-000000' / 'trace.json').is_file())
                self.assertFalse((self.output / 'case-000001').exists())


if __name__ == '__main__':
    unittest.main()
