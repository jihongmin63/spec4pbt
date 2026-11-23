"""Normal replay reads the implementation's observed values."""
from pathlib import Path
import sys
import tempfile
import unittest

from scripts.property.compiler import compile_debug, compile_replay, compile_spec
from scripts.property.replay import replay


ROOT = Path(__file__).resolve().parents[2]
DEMO = ROOT / 'properties/property_replay_demo'
SPEC = ROOT / 'specification/property_replay_demo/source/Property.watsup'
INPUT = {'x': {'type': 'nat', 'value': '7'}}


class ReplayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.program = compile_replay(compile_spec(SPEC, DEMO / 'Property.toml'))

    def run_with(self, script, timeout=5):
        return replay(self.program, INPUT,
                      {'demo_external': [sys.executable, str(script)]},
                      timeout=timeout)

    def test_actual_b20_produces_c21_and_failed_goal(self):
        result = self.run_with(ROOT / 'adapters/property_replay_demo/demo_external.py')
        self.assertEqual(result.status, 'failed')
        self.assertEqual(result.external_call_count, 1)
        self.assertEqual(result.trace['external_calls'][0]['outputs'][0]['value']['value'], '20')
        self.assertTrue(any(item['value'] == {'type': 'nat', 'value': '21'}
                            for item in result.trace['bindings']))

    def test_adapter_no_match_makes_precondition_implementation_bug(self):
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            script = Path(temp) / 'no_match.py'
            script.write_text('import sys,json\nfor line in sys.stdin:\n'
                              ' print(json.dumps({"status":"no_match","fresh_id":0}),flush=True)\n')
            result = self.run_with(script)
        self.assertEqual(result.status, 'implementation_bug')

    def test_adapter_timeout_and_protocol_error_take_priority(self):
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            script = Path(temp) / 'bad.py'
            script.write_text('import time,sys\nfor line in sys.stdin: time.sleep(2)\n')
            self.assertEqual(self.run_with(script, timeout=0.2).status, 'unknown')
            script.write_text('import sys\nfor line in sys.stdin: print("{}",flush=True)\n')
            self.assertEqual(self.run_with(script).status, 'execution_error')

    def test_external_dependent_internal_failure_is_implementation_bug(self):
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            source = Path(temp) / 'Property.watsup'
            source.write_text(SPEC.read_text().replace(
                '  -- if c = $(b + 1)',
                '  -- if c = $(b + 1)\n  -- if b = 10'))
            program = compile_replay(compile_spec(source, DEMO / 'Property.toml'))
            result = replay(program, INPUT, {'demo_external': [
                sys.executable, str(ROOT / 'adapters/property_replay_demo/demo_external.py')]})
        self.assertEqual(result.status, 'implementation_bug')
        self.assertEqual(result.reason, 'external_dependent_premise_failure')
        self.assertTrue(result.trace['failure']['external_events'])
        self.assertIn('Property.watsup', result.trace['failure']['source'])

    def test_external_independent_internal_failure_is_execution_error(self):
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            source = Path(temp) / 'Property.watsup'
            source.write_text(SPEC.read_text().replace(
                '  -- B: b c', '  -- B: b c\n  -- if x = 8'))
            program = compile_replay(compile_spec(source, DEMO / 'Property.toml'))
            result = replay(program, INPUT, {'demo_external': [
                sys.executable, str(ROOT / 'adapters/property_replay_demo/demo_external.py')]})
        self.assertEqual(result.status, 'execution_error')
        self.assertEqual(result.reason, 'unexpected_internal_premise_failure')
        self.assertEqual(result.external_call_count, 1)
        self.assertEqual(result.trace['failure']['external_events'], [])

    def test_goal_only_external_with_and_without_spec_definition(self):
        fixture = ROOT / 'scripts/tests/fixtures/property/bridge/goal_only.watsup'
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            directory = Path(temp)
            config = directory / 'Property.toml'
            config.write_text('precondition = "Pre"\ngoal = "Goal"\n'
                              '[[external]]\nrelation = "EGoal"\n'
                              'adapter = "goal"\nconversion = "json-v1"\n'
                              'observed_outputs = []\n')
            adapter = directory / 'goal.py'
            adapter.write_text('import json,sys\nfor line in sys.stdin:\n'
                               ' request=json.loads(line)\n'
                               ' print(json.dumps({"status":"returned","outputs":[],"fresh_id":request["fresh_id"]}),flush=True)\n')
            source = directory / 'defined.watsup'
            source.write_text(fixture.read_text().replace(
                'extern relation EGoal: nat nat hint(input %0)',
                'relation EGoal: nat nat hint(input %0)\n'
                'rule EGoal/main: x r\n  -- if r = x'))
            for candidate, available in ((fixture, False), (source, True)):
                model = compile_spec(candidate, config)
                self.assertEqual(compile_debug(model).available, available)
                result = replay(compile_replay(model), INPUT,
                                {'goal': [sys.executable, str(adapter)]})
                self.assertEqual(result.status, 'passed', result)
                self.assertEqual(result.external_call_count, 1)
                self.assertEqual(result.trace['external_calls'][0]['relation'], 'EGoal')

    def test_returned_fresh_id_taints_later_helper_condition(self):
        fixture = ROOT / 'scripts/tests/fixtures/property/bridge/nested_fresh.watsup'
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            directory = Path(temp)
            source = directory / 'nested_fresh.watsup'
            source.write_text(fixture.read_text().replace(
                '  -- if z = y', '  -- if t = "FRESH__0"\n  -- if z = y'))
            config = directory / 'Property.toml'
            config.write_text('precondition = "Pre"\ngoal = "Goal"\n'
                              '[[external]]\nrelation = "E1"\n'
                              'adapter = "fresh"\nconversion = "json-v1"\n'
                              'observed_outputs = [0]\n')
            adapter = directory / 'fresh.py'
            adapter.write_text('import json,sys\nfor line in sys.stdin:\n'
                               ' print(json.dumps({"status":"returned","outputs":[{"position":0,"value":{"type":"nat","value":"7"}}],"fresh_id":1}),flush=True)\n')
            model = compile_spec(source, config)
            result = replay(compile_replay(model),
                            {'x': {'type': 'nat', 'value': '5'}},
                            {'fresh': [sys.executable, str(adapter)]})
        self.assertEqual(result.status, 'implementation_bug', result)
        self.assertEqual(result.trace['fresh_id'], 2)
        self.assertTrue(result.trace['failure']['external_events'])
        self.assertTrue(any(edge['binding'] == 'H.t'
                            for edge in result.trace['failure']['dependencies']))

    def test_recovered_branch_does_not_taint_independent_fallback_failure(self):
        fixture = ROOT / 'scripts/tests/fixtures/property/bridge/fallback_fresh.watsup'
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            directory = Path(temp)
            source = directory / 'fallback_fresh.watsup'
            source.write_text(fixture.read_text().replace(
                '  -- if t = $fresh_typeId()\nrule Choice/second',
                '  -- if y = 7\n  -- if x = 8\n'
                '  -- if t = $fresh_typeId()\nrule Choice/second', 1).replace(
                'rule Choice/second: x t\n',
                'rule Choice/second: x t\n  -- if x = 9\n', 1))
            config = directory / 'Property.toml'
            config.write_text('precondition = "Pre"\ngoal = "Goal"\n'
                              '[[external]]\nrelation = "E1"\n'
                              'adapter = "first"\nconversion = "json-v1"\n'
                              'observed_outputs = [0]\n')
            adapter = directory / 'first.py'
            adapter.write_text('import json,sys\nfor line in sys.stdin:\n'
                               ' print(json.dumps({"status":"returned","outputs":[{"position":0,"value":{"type":"nat","value":"7"}}],"fresh_id":0}),flush=True)\n')
            model = compile_spec(source, config)
            result = replay(compile_replay(model),
                            {'x': {'type': 'nat', 'value': '5'}},
                            {'first': [sys.executable, str(adapter)]})
        self.assertEqual(result.status, 'execution_error', result)
        self.assertEqual(result.external_call_count, 1)
        self.assertEqual(result.reason, 'unexpected_internal_premise_failure')


if __name__ == '__main__':
    unittest.main()
