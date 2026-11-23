"""Exercise the pinned frontend and native AL interpreter through the bridge."""
from pathlib import Path
import json
import subprocess
import unittest

from scripts.property.bridge import build_bridge
from scripts.property.engine import run_bridge


ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / 'scripts/tests/fixtures/property/bridge'


class BridgeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.executable = build_bridge()

    def call(self, *arguments, stdin=''):
        process = subprocess.run(
            ['bash', str(ROOT / 'environment/env.sh'), 'frontend',
             str(self.executable), *map(str, arguments)],
            input=stdin, capture_output=True, text=True, timeout=90)
        return process

    def test_frontend_reports_binding_error_with_source(self):
        result = self.call('check', FIXTURE / 'unbound.watsup')
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('unbound.watsup', result.stdout + result.stderr)

    def test_check_and_debug_native_relations(self):
        result = self.call('check', FIXTURE / 'basic.watsup')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = json.loads(result.stdout)
        self.assertIn('Pre', report['relations'])
        self.assertIn('Goal', report['relations'])
        request = json.dumps({'input': [{'type': 'nat', 'value': 7}],
                              'pre': 'Pre', 'goal': 'Goal'}) + '\n'
        result = self.call('debug', FIXTURE / 'basic.watsup', stdin=request)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = json.loads(result.stdout)
        self.assertEqual(report['status'], 'passed')
        self.assertEqual(report['pre_outputs'], [{'type': 'nat', 'value': '7'}])
        self.assertTrue(any(item['label'].endswith('Pre.return.y')
                            for item in report['bindings']))
        self.assertTrue(all('basic.watsup' in item['source']
                            for item in report['bindings']))

    def test_fresh_state_flows_through_pre_and_goal(self):
        request = json.dumps({'input': [{'type': 'nat', 'value': 7}],
                              'pre': 'Pre', 'goal': 'Goal'}) + '\n'
        for _ in range(2):
            result = self.call('debug', FIXTURE / 'fresh.watsup', stdin=request)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            report = json.loads(result.stdout)
            self.assertEqual(report['status'], 'passed')
            self.assertEqual(report['pre_outputs'], [
                {'type': 'text', 'value': 'FRESH__0'},
                {'type': 'text', 'value': 'FRESH__1'}])
            self.assertEqual(report['goal_outputs'], [
                {'type': 'text', 'value': 'FRESH__2'}])
            self.assertEqual(report['fresh_id'], 3)
            self.assertTrue(any(item['value'] == {'type': 'text', 'value': 'FRESH__1'}
                                for item in report['bindings']))

    def test_partial_observation_executes_without_dummy_value(self):
        program = [str(ROOT / 'environment/env.sh'), 'frontend',
                   str(self.executable), 'replay', str(FIXTURE / 'partial.watsup')]
        for first_positions in ([0, 1], [0]):
            process = subprocess.Popen(['bash', *program], stdin=subprocess.PIPE,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                       text=True)
            def send(payload):
                process.stdin.write(json.dumps(payload) + '\n')
                process.stdin.flush()
            send({'input': [{'type': 'nat', 'value': 5}],
                  'pre': 'Pre', 'goal': 'Goal',
                  'external': [{'relation': 'E1', 'observed_outputs': first_positions},
                               {'relation': 'E2', 'observed_outputs': [0]}]})
            event = json.loads(process.stdout.readline())
            self.assertEqual(event['relation'], 'E1')
            self.assertEqual(event['observed_outputs'], first_positions)
            values = [7, 99] if len(first_positions) == 2 else [7]
            send({'status': 'returned', 'fresh_id': 0,
                  'outputs': [{'position': p, 'value': {'type': 'nat', 'value': v}}
                              for p, v in zip(first_positions, values)]})
            event = json.loads(process.stdout.readline())
            self.assertEqual(event['relation'], 'E2')
            self.assertEqual(event['input'], [{'type': 'nat', 'value': '7'}])
            send({'status': 'returned', 'fresh_id': 0,
                  'outputs': [{'position': 0, 'value': {'type': 'nat', 'value': 8}}]})
            result = json.loads(process.stdout.readline())
            self.assertEqual(result['status'], 'passed')
            self.assertEqual(result['pre_outputs'], [{'type': 'nat', 'value': '8'}])
            code = process.wait(timeout=30)
            stderr = process.stderr.read()
            process.stdin.close()
            process.stdout.close()
            process.stderr.close()
            self.assertEqual(code, 0, stderr)

    def test_native_first_success_does_not_research_after_later_failure(self):
        request = json.dumps({'input': [{'type': 'nat', 'value': 5}],
                              'pre': 'Pre', 'goal': 'Goal'}) + '\n'
        result = self.call('debug', FIXTURE / 'first_success.watsup', stdin=request)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = json.loads(result.stdout)
        self.assertEqual(report['status'], 'precondition_failed')
        self.assertTrue(any(item['label'] == 'Choice.return.z' and
                            item['value'] == {'type': 'nat', 'value': '0'}
                            for item in report['bindings']))

    def test_nested_external_response_advances_same_fresh_counter(self):
        events = []
        def callback(event):
            events.append(event)
            return {'status': 'returned', 'fresh_id': 1,
                    'outputs': [{'position': 0,
                                 'value': {'type': 'nat', 'value': '7'}}]}
        report = run_bridge('replay', FIXTURE / 'nested_fresh.watsup',
                            {'input': [{'type': 'nat', 'value': '5'}],
                             'pre': 'Pre', 'goal': 'Goal',
                             'external': [{'relation': 'E1', 'observed_outputs': [0]}]},
                            callback=callback)
        self.assertEqual(report['status'], 'passed')
        self.assertEqual(events[0]['fresh_id'], 0)
        self.assertEqual(report['fresh_id'], 2)
        self.assertTrue(any(item['value'] == {'type': 'text', 'value': 'FRESH__1'}
                            for item in report['bindings']))
        self.assertEqual(report['external_calls'][0]['fresh_after'], 1)

    def test_no_match_preserves_counter_for_native_fallback_rule(self):
        report = run_bridge('replay', FIXTURE / 'fallback_fresh.watsup',
                            {'input': [{'type': 'nat', 'value': '5'}],
                             'pre': 'Pre', 'goal': 'Goal',
                             'external': [{'relation': 'E1', 'observed_outputs': [0]}]},
                            callback=lambda _: {'status': 'no_match', 'fresh_id': 1})
        self.assertEqual(report['status'], 'passed')
        self.assertEqual(report['pre_outputs'],
                         [{'type': 'text', 'value': 'FRESH__1'}])
        self.assertEqual(report['fresh_id'], 2)


if __name__ == '__main__':
    unittest.main()
