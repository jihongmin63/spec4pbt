"""Run named ADT Inputs and adapter outputs through the native property path."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

from scripts.property.compiler import compile_debug, compile_replay, compile_spec
from scripts.property.debug import debug
from scripts.property.generation import GenerationError, load_samples
from scripts.property.replay import replay


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'scripts/tests/fixtures/property/bridge/typed_input.watsup'
EMPTY = {'type': 'tree', 'constructor': 'EMPTY', 'args': []}
TREE = {'type': 'tree', 'constructor': 'NODE', 'args': [
    {'type': 'tree', 'constructor': 'LEAF', 'args': [
        {'type': 'nat', 'value': '7'}, {'type': 'text', 'value': 'quote " \\ 한글'}]},
    EMPTY]}
INPUT = {'t': TREE, 'n': {'type': 'nat', 'value': '4'},
         'i': {'type': 'int', 'value': '-19'},
         's': {'type': 'text', 'value': 'line\nnext'},
         'b': {'type': 'bool', 'value': True}}


class TypedTransportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        checks = ROOT / '_opam-testing-theorems/checks'
        cls.evidence = Path(tempfile.mkdtemp(prefix='typed-transport.', dir=checks))
        config = cls.evidence / 'Property.toml'
        config.write_text('precondition = "Pre"\ngoal = "Goal"\n'
                          '[[external]]\nrelation = "E"\nadapter = "tree_adapter"\n'
                          'conversion = "json-v1"\nobserved_outputs = [0]\n')
        cls.model = compile_spec(SOURCE, config)
        cls.debug_program = compile_debug(cls.model)
        cls.replay_program = compile_replay(cls.model)

    def test_samples_decode_frontend_constructor_metadata(self):
        self.assertIn('tree', getattr(self.model, 'type_schema', {}),
                      'frontend constructor schema must reach the property model')
        samples = load_samples([None, INPUT], self.model.inputs,
                               self.model.type_schema)
        self.assertEqual(samples, [None, INPUT])
        wrong = copy.deepcopy(INPUT)
        wrong['t']['args'][0]['args'][0]['type'] = 'int'
        with self.assertRaises(GenerationError):
            load_samples([wrong], self.model.inputs, self.model.type_schema)

    def test_debug_executes_named_constructor_inputs_without_adapters(self):
        result = debug(self.debug_program, INPUT)
        self.assertEqual(result.status, 'passed', result.reason)
        self.assertEqual(result.external_call_count, 0)
        self.assertEqual(result.trace['pre_outputs'], [TREE])
        self.assertTrue(any(binding['value'] == TREE
                            for binding in result.trace['bindings']))
        self.assertTrue(all('typed_input.watsup' in binding['source']
                            for binding in result.trace['bindings']))

    def adapter(self, value):
        script = self.evidence / 'adapter.py'
        # Assert the request retains the same typed constructor tree that the
        # normal bridge received; produce an independent observed output.
        script.write_text('import json,sys\nrequest=json.loads(sys.stdin.readline())\n'
                          'assert request["input"] == ' + repr([TREE]) + '\n'
                          'print(json.dumps({"status":"returned",'
                          '"fresh_id":request["fresh_id"],"outputs":'
                          '[{"position":0,"value":' + repr(value) + '}]}),flush=True)\n')
        return {'tree_adapter': [sys.executable, str(script)]}

    def test_replay_uses_actual_named_constructor_output(self):
        result = replay(self.replay_program, INPUT, self.adapter(EMPTY))
        self.assertEqual(result.status, 'failed', result.reason)
        self.assertEqual(result.external_call_count, 1)
        self.assertEqual(result.trace['external_calls'][0]['outputs'][0]['value'], EMPTY)
        self.assertEqual(result.trace['pre_outputs'], [EMPTY])
        self.assertEqual(replay(self.replay_program, INPUT,
                                self.adapter(TREE)).status, 'passed')

    def test_replay_rejects_invalid_observed_constructor_or_arity(self):
        for value in ({'type': 'tree', 'constructor': 'UNKNOWN', 'args': []},
                      {'type': 'tree', 'constructor': 'NODE', 'args': [EMPTY]}):
            with self.subTest(value=value):
                result = replay(self.replay_program, INPUT, self.adapter(value))
                self.assertEqual(result.status, 'execution_error')
                self.assertEqual(result.external_call_count, 1)
                self.assertRegex(result.reason, 'unknown tree constructor|arity mismatch')


if __name__ == '__main__':
    unittest.main()
