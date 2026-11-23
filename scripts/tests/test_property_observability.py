"""Compile-time K propagation over typed AL relation calls."""
from pathlib import Path
import tempfile
import unittest

from scripts.property.compiler import CompileError, analyze_replay, compile_spec


ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / 'scripts/tests/fixtures/property/bridge'


class ObservabilityTests(unittest.TestCase):
    def model(self, source='partial.watsup', first=(0,), whole_helper=False):
        text = (FIXTURE / 'Property.toml').read_text()
        text = text.replace('observed_outputs = [0]',
                            'observed_outputs = [' + ', '.join(map(str, first)) + ']', 1)
        if whole_helper:
            text += ('\n[[external]]\nrelation = "H"\n'
                     'adapter = "whole_helper"\nconversion = "json-v1"\n'
                     'observed_outputs = [0]\n')
        directory = tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems')
        self.addCleanup(directory.cleanup)
        config = Path(directory.name) / 'Property.toml'
        config.write_text(text)
        return compile_spec(FIXTURE / source, config)

    def test_unused_unobserved_slot_is_allowed(self):
        report = analyze_replay(self.model())
        self.assertIn(0, report['guaranteed_outputs']['Pre'])
        self.assertEqual(report['projection']['E1'], [0])
        self.assertEqual(len(report['al_md5']), 32)
        calls = [item for item in report['premises'] if item['relation'] == 'Pre']
        self.assertEqual([item['kind'] for item in calls], ['E1', 'E2'])
        self.assertIn('x', calls[0]['known_before'])
        self.assertIn('y', calls[0]['introduced'])
        self.assertNotIn('u', calls[0]['known_after'])
        self.assertIn('y', calls[1]['required'])
        self.assertIn('partial.watsup', calls[1]['source'])

    def test_missing_y_reports_producer_and_consumer(self):
        with self.assertRaises(CompileError) as caught:
            analyze_replay(self.model(first=()))
        diagnostic = str(caught.exception)
        self.assertIn('y', diagnostic)
        self.assertIn('E1', diagnostic)
        self.assertIn('E2', diagnostic)
        self.assertIn('partial.watsup', diagnostic)

    def test_used_unobserved_u_is_rejected(self):
        with self.assertRaises(CompileError) as caught:
            analyze_replay(self.model(source='partial_used_u.watsup'))
        self.assertIn('u', str(caught.exception))

    def test_helper_classification_does_not_hide_nested_obligation(self):
        report = analyze_replay(self.model(source='helper.watsup'))
        self.assertTrue(report['external_classification']['H'])
        self.assertEqual(report['guaranteed_outputs']['H'], [0])
        with self.assertRaises(CompileError) as caught:
            analyze_replay(self.model(source='helper.watsup', first=()))
        self.assertIn('consumer E2', str(caught.exception))

    def test_nested_whole_helper_adapter_is_rejected(self):
        with self.assertRaises(CompileError) as caught:
            analyze_replay(self.model(source='helper.watsup', whole_helper=True))
        self.assertIn('nested boundary', str(caught.exception))

    def test_multiple_rules_intersect_guaranteed_outputs(self):
        with self.assertRaises(CompileError) as caught:
            analyze_replay(self.model(source='multi_rule.watsup'))
        self.assertIn('Pre public output slot 0 unavailable', str(caught.exception))


if __name__ == '__main__':
    unittest.main()
