"""Native helper calls preserve external control and recursive data dependencies."""
from dataclasses import asdict
import json
from pathlib import Path
import sys
import tempfile
import unittest

from scripts.property.bridge import ROOT
from scripts.property.compiler import compile_replay, compile_spec
from scripts.property.replay import replay


FIXTURES = ROOT / 'scripts/tests/fixtures/property/bridge'


class DependencyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.evidence = Path(tempfile.mkdtemp(prefix='property-dependency.',
                           dir=ROOT / '_opam-testing-theorems/checks'))

    def execute(self, fixture, value, observed, pre='Pre', fresh=None):
        directory = Path(tempfile.mkdtemp(prefix=fixture + '.', dir=self.evidence))
        config = directory / 'Property.toml'
        config.write_text(f'precondition = "{pre}"\ngoal = "Goal"\n'
                          '[[external]]\nrelation = "E"\nadapter = "test"\n'
                          'conversion = "json-v1"\nobserved_outputs = [0]\n')
        adapter = directory / 'adapter.py'
        adapter.write_text('import json,sys\nrequest=json.loads(sys.stdin.readline())\n'
                           'print(json.dumps({"status":"returned",'
                           '"fresh_id":' + ('request["fresh_id"]' if fresh is None else str(fresh)) +
                           ',"outputs":[{"position":0,'
                           '"value":{"type":"nat","value":' + repr(str(observed)) +
                           '}}]}),flush=True)\n')
        model = compile_spec(FIXTURES / (fixture + '.watsup'), config)
        result = replay(compile_replay(model),
                        {'x': {'type': 'nat', 'value': str(value)}},
                        {'test': [sys.executable, str(adapter)]})
        (directory / 'result.json').write_text(json.dumps(asdict(result), indent=2) + '\n')
        return result

    def test_zero_output_helper_propagates_successful_guard_control(self):
        result = self.execute('dependency_guard', 7, 7)
        self.assertEqual(result.status, 'implementation_bug', result)
        self.assertEqual(result.external_call_count, 1)
        self.assertEqual(result.trace['failure']['relation'], 'Pre')
        self.assertEqual(len(result.trace['failure']['external_events']), 1)

    def test_mutual_recursion_keeps_external_input_dependencies(self):
        result = self.execute('dependency_mutual', 2, 0)
        self.assertEqual(result.status, 'implementation_bug', result)
        self.assertEqual(result.external_call_count, 1)
        self.assertEqual(result.trace['failure']['relation'], 'Pre')
        self.assertEqual(len(result.trace['failure']['external_events']), 1)
        self.assertTrue(any(binding['label'] == 'A.input.n' and
                            binding['value'] == {'type': 'nat', 'value': '0'}
                            for binding in result.trace['bindings']))

    def test_other_helper_argument_does_not_taint_independent_failure(self):
        result = self.execute('dependency_guard', 7, 7, pre='PreIndependent')
        self.assertEqual(result.status, 'execution_error', result)
        self.assertEqual(result.external_call_count, 1)
        self.assertEqual(result.trace['failure']['relation'], 'Independent')
        self.assertEqual(result.trace['failure']['external_events'], [])

    def test_nested_function_return_taints_computed_binding(self):
        result = self.execute('dependency_function', 7, 20)
        self.assertEqual(result.status, 'implementation_bug', result)
        self.assertEqual(result.external_call_count, 1)
        self.assertEqual(result.trace['failure']['relation'], 'Pre')
        self.assertEqual(len(result.trace['failure']['external_events']), 1)

    def test_nested_function_ignored_argument_does_not_taint_result(self):
        result = self.execute('dependency_function', 7, 20, pre='PreIgnored')
        self.assertEqual(result.status, 'execution_error', result)
        self.assertEqual(result.external_call_count, 1)
        self.assertEqual(result.trace['failure']['external_events'], [])

    def test_nested_function_guard_taints_continuation(self):
        result = self.execute('dependency_function', 7, 20, pre='PreControl')
        self.assertEqual(result.status, 'implementation_bug', result)
        self.assertEqual(result.external_call_count, 1)
        self.assertEqual(len(result.trace['failure']['external_events']), 1)

    def test_nested_recursive_function_retains_external_argument(self):
        result = self.execute('dependency_function', 7, 20, pre='PreRecursive')
        self.assertEqual(result.status, 'implementation_bug', result)
        self.assertEqual(result.external_call_count, 1)
        self.assertEqual(len(result.trace['failure']['external_events']), 1)

    def test_nested_function_failure_uses_only_its_relevant_argument(self):
        result = self.execute('dependency_function', 7, 20, pre='PreInnerIndependent')
        self.assertEqual(result.status, 'execution_error', result)
        self.assertEqual(result.external_call_count, 1)
        self.assertEqual(result.trace['failure']['relation'], '$independent')
        self.assertEqual(result.trace['failure']['external_events'], [])

    def test_nested_fresh_before_external_does_not_inherit_later_state(self):
        result = self.execute('dependency_function_fresh', 7, 20, fresh=5)
        self.assertEqual(result.status, 'execution_error', result)
        self.assertEqual(result.external_call_count, 1)
        self.assertEqual(result.trace['fresh_id'], 5)
        self.assertEqual(result.trace['failure']['external_events'], [])
        self.assertTrue(any(binding['label'] == 'Pre.t' and
                            binding['value'] == {'type': 'text', 'value': 'FRESH__0'}
                            for binding in result.trace['bindings']))

    def test_nested_fresh_after_external_inherits_actual_state(self):
        result = self.execute('dependency_function_fresh', 7, 20,
                              pre='PreLater', fresh=5)
        self.assertEqual(result.status, 'implementation_bug', result)
        self.assertEqual(result.external_call_count, 1)
        self.assertEqual(result.trace['fresh_id'], 6)
        self.assertEqual(len(result.trace['failure']['external_events']), 1)
        self.assertTrue(any(binding['label'] == 'PreLater.t' and
                            binding['value'] == {'type': 'text', 'value': 'FRESH__5'}
                            for binding in result.trace['bindings']))


if __name__ == '__main__':
    unittest.main()
