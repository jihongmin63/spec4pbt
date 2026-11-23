"""Debug evaluates the fixed specification without an adapter."""
from pathlib import Path
import tempfile
import unittest

from scripts.property.compiler import CompileError, compile_debug, compile_replay, compile_spec
from scripts.property.debug import debug


ROOT = Path(__file__).resolve().parents[2]
DEMO = ROOT / 'properties/property_replay_demo'
SPEC = ROOT / 'specification/property_replay_demo/source/Property.watsup'


class DebugTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.program = compile_debug(compile_spec(SPEC, DEMO / 'Property.toml'))

    def test_spec_b10_c11_passes_at_x7_without_adapter(self):
        result = debug(self.program, {'x': {'type': 'nat', 'value': '7'}})
        self.assertEqual(result.status, 'passed')
        self.assertEqual(result.external_call_count, 0)
        values = [item['value']['value'] for item in result.trace['bindings']]
        self.assertIn('10', values)
        self.assertIn('11', values)

    def test_wrong_goal_fails_without_filtering_input(self):
        result = debug(self.program, {'x': {'type': 'nat', 'value': '8'}})
        self.assertEqual(result.status, 'failed')
        self.assertEqual(result.external_call_count, 0)

    def test_debug_survives_normal_observation_failure(self):
        fixture = ROOT / 'scripts/tests/fixtures/property/bridge'
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            config = Path(temp) / 'Property.toml'
            config.write_text((fixture / 'Property.toml').read_text().replace(
                'observed_outputs = [0]', 'observed_outputs = []', 1))
            model = compile_spec(fixture / 'defined_partial.watsup', config)
            with self.assertRaises(CompileError):
                compile_replay(model)
            result = debug(compile_debug(model),
                           {'x': {'type': 'nat', 'value': '5'}})
            self.assertEqual(result.status, 'passed')
            self.assertEqual(result.external_call_count, 0)

    def test_missing_goal_only_definition_is_unavailable(self):
        fixture = ROOT / 'scripts/tests/fixtures/property/bridge'
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            config = Path(temp) / 'Property.toml'
            config.write_text('precondition = "Pre"\ngoal = "Goal"\n'
                              '[[external]]\nrelation = "EGoal"\n'
                              'adapter = "example"\nconversion = "json-v1"\n'
                              'observed_outputs = []\n')
            model = compile_spec(fixture / 'goal_only.watsup', config)
            self.assertIsNotNone(compile_replay(model))
            result = debug(compile_debug(model),
                           {'x': {'type': 'nat', 'value': '5'}})
            self.assertEqual(result.status, 'unavailable')
            self.assertIn('EGoal', result.reason)

    def test_precondition_failure_keeps_typed_bindings(self):
        fixture = ROOT / 'scripts/tests/fixtures/property/bridge'
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            config = Path(temp) / 'Property.toml'
            config.write_text('precondition = "Pre"\ngoal = "Goal"\n')
            model = compile_spec(fixture / 'pre_fail.watsup', config)
            result = debug(compile_debug(model),
                           {'x': {'type': 'nat', 'value': '5'}})
            self.assertEqual(result.status, 'precondition_failed')
            self.assertTrue(any(item['value'] == {'type': 'nat', 'value': '5'}
                                for item in result.trace['bindings']))
            self.assertEqual(result.trace['failure']['reason'],
                             'specification_precondition_failed')
            self.assertIn('pre_fail.watsup', result.trace['failure']['source'])

    def test_debug_fresh_starts_at_zero_and_reaches_goal(self):
        fixture = ROOT / 'scripts/tests/fixtures/property/bridge'
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            config = Path(temp) / 'Property.toml'
            config.write_text('precondition = "Pre"\ngoal = "Goal"\n')
            model = compile_spec(fixture / 'fresh.watsup', config)
            for _ in range(2):
                result = debug(compile_debug(model),
                               {'x': {'type': 'nat', 'value': '5'}})
                self.assertEqual(result.status, 'passed')
                self.assertEqual(result.trace['fresh_id'], 3)
                self.assertEqual([x['value'] for x in result.trace['pre_outputs']],
                                 ['FRESH__0', 'FRESH__1'])
                self.assertEqual(result.trace['goal_outputs'][0]['value'], 'FRESH__2')


if __name__ == '__main__':
    unittest.main()
