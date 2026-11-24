"""Tracing records native selected-path values without repeating evaluation."""
import json
from pathlib import Path
import tempfile
import unittest

from scripts.property.bridge import ROOT
from scripts.property.dependency import failed_premise
from scripts.property.engine import run_bridge


FIXTURES = ROOT / 'scripts/tests/fixtures/property/bridge'
NAT = {'type': 'nat', 'value': '7'}


class InstrumentationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.evidence = Path(tempfile.mkdtemp(prefix='property-trace.',
                            dir=ROOT / '_opam-testing-theorems/checks'))

    def compare(self, fixture, value):
        traces = []
        for instrument in (False, True):
            trace = run_bridge('debug', FIXTURES / (fixture + '.watsup'),
                               {'pre': 'Pre', 'goal': 'Goal', 'input': [value],
                                'instrument': instrument})
            (self.evidence / (fixture + ('-on' if instrument else '-off') + '.json')).write_text(
                json.dumps(trace, indent=2) + '\n')
            traces.append(trace)
        for field in ('status', 'pre_outputs', 'goal_outputs', 'fresh_id'):
            self.assertEqual(traces[0][field], traces[1][field], field)
        self.assertEqual(traces[0]['bindings'], [])
        self.assertEqual(traces[0]['markers'], [])
        return traces[1]

    def binding(self, trace, label, value):
        matched = [binding for binding in trace['bindings']
                   if binding['label'] == label and binding['value'] == value]
        self.assertTrue(matched, f'missing typed binding {label} = {value}')
        self.assertTrue(all('.watsup:' in item['source'] for item in matched))

    def test_computed_returns_and_nested_function_bindings_preserve_fresh(self):
        trace = self.compare('trace_computed', NAT)
        self.assertEqual(trace['status'], 'passed')
        self.assertEqual(trace['pre_outputs'], [
            {'type': 'nat', 'value': '9'},
            {'type': 'text', 'value': 'FRESH__0'},
            {'type': 'text', 'value': 'FRESH__1'}])
        self.assertEqual(trace['goal_outputs'], [{'type': 'text', 'value': 'FRESH__2'}])
        self.assertEqual(trace['fresh_id'], 3)
        for label, value in (
            ('Helper.input.n', NAT),
            ('Helper.return.0', {'type': 'nat', 'value': '8'}),
            ('$nested.input.n', NAT),
            ('$nested.m', {'type': 'nat', 'value': '8'}),
            ('$nested.return.0', {'type': 'nat', 'value': '9'}),
            ('$outer.return.0', {'type': 'nat', 'value': '9'}),
            ('Pre.return.1', {'type': 'text', 'value': 'FRESH__0'}),
            ('Pre.return.2', {'type': 'text', 'value': 'FRESH__1'}),
        ):
            self.binding(trace, label, value)

    def test_common_match_premises_record_destructured_typed_values(self):
        value = {'type': 'token', 'constructor': 'BOX', 'args': [NAT]}
        trace = self.compare('trace_match', value)
        self.assertEqual(trace['status'], 'passed')
        self.binding(trace, 'OnlyBox.input.t', value)
        self.binding(trace, 'OnlyBox.n', NAT)
        self.binding(trace, 'OnlyBox.return.0', {'type': 'nat', 'value': '8'})

    def test_common_match_failure_reports_the_inner_source_before_body(self):
        value = {'type': 'token', 'constructor': 'OTHER', 'args': []}
        trace = self.compare('trace_match', value)
        self.assertEqual(trace['status'], 'precondition_failed')
        failure = failed_premise(trace)
        self.assertEqual(failure['relation'], 'OnlyBox')
        self.assertEqual(failure['premise'], 'if')
        self.assertIn('trace_match.watsup:7.', failure['source'])
        self.binding(trace, 'OnlyBox.input.t', value)
        self.assertFalse(any(item['label'].startswith('OnlyBox.return.')
                             for item in trace['bindings']))

    def test_failed_function_clause_preserves_consumed_fresh_for_fallback(self):
        trace = self.compare('trace_fallback', NAT)
        self.assertEqual(trace['status'], 'passed')
        self.assertEqual(trace['pre_outputs'], [
            {'type': 'text', 'value': 'FRESH__1'},
            {'type': 'text', 'value': 'FRESH__2'}])
        self.assertEqual(trace['fresh_id'], 3)
        self.binding(trace, '$recover.a', {'type': 'text', 'value': 'FRESH__0'})
        self.binding(trace, '$recover.return.0', {'type': 'text', 'value': 'FRESH__1'})

    def test_earlier_expression_failure_prevents_later_function_effects(self):
        traces = []
        for instrument in (False, True):
            calls = []

            def external(request):
                calls.append(request)
                return {'status': 'returned', 'fresh_id': request['fresh_id'],
                        'outputs': [{'position': 0, 'value': NAT}]}

            trace = run_bridge('replay', FIXTURES / 'trace_early_failure.watsup',
                               {'pre': 'Pre', 'goal': 'Goal', 'input': [NAT],
                                'external': [{'relation': 'E', 'observed_outputs': [0]}],
                                'projection': {'E': [0]}, 'instrument': instrument},
                               callback=external)
            evidence = {'trace': trace, 'external_call_count': len(calls)}
            (self.evidence / ('trace_early_failure-' + ('on' if instrument else 'off') +
                              '.json')).write_text(json.dumps(evidence, indent=2) + '\n')
            self.assertEqual(trace['status'], 'precondition_failed')
            self.assertEqual(len(calls), 0)
            self.assertEqual(trace['external_calls'], [])
            self.assertEqual(trace['fresh_id'], 0)
            self.assertFalse(any(marker['relation'] == '$later'
                                 for marker in trace['markers']))
            traces.append(trace)
        for field in ('status', 'pre_outputs', 'goal_outputs', 'external_calls', 'fresh_id'):
            self.assertEqual(traces[0][field], traces[1][field], field)

    def test_tracing_keeps_native_first_success_rule_choice(self):
        trace = self.compare('first_success', NAT)
        self.assertEqual(trace['status'], 'precondition_failed')
        self.binding(trace, 'Choice.return.z', {'type': 'nat', 'value': '0'})
        self.assertFalse(any(item['value'] == {'type': 'nat', 'value': '1'}
                             for item in trace['bindings']))


if __name__ == '__main__':
    unittest.main()
