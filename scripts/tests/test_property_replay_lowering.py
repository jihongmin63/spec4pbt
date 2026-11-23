"""A projected helper runs with native AL and no fabricated output."""
from pathlib import Path
import json
import subprocess
import unittest

from scripts.property.bridge import ROOT, build_bridge
from scripts.property.compiler import compile_replay, compile_spec


FIXTURE = ROOT / 'scripts/tests/fixtures/property/bridge'


class ReplayLoweringTests(unittest.TestCase):
    def test_unobserved_helper_output_is_removed_at_every_boundary(self):
        program = compile_replay(compile_spec(FIXTURE / 'helper_extra.watsup',
                                              FIXTURE / 'Property.toml'))
        self.assertEqual(program.projection['E1'], [0])
        self.assertEqual(program.projection['H'], [0])
        executable = build_bridge()
        process = subprocess.Popen(
            ['bash', str(ROOT / 'environment/env.sh'), 'frontend',
             str(executable), 'replay', str(FIXTURE / 'helper_extra.watsup')],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, text=True)
        def send(payload):
            process.stdin.write(json.dumps(payload) + '\n')
            process.stdin.flush()
        send({'pre': 'Pre', 'goal': 'Goal',
              'input': [{'type': 'nat', 'value': 5}],
              'external': list(program.model.external),
              'projection': program.projection})
        event = json.loads(process.stdout.readline())
        self.assertEqual(event['relation'], 'E1')
        send({'status': 'returned', 'fresh_id': 0,
              'outputs': [{'position': 0,
                           'value': {'type': 'nat', 'value': 7}}]})
        event = json.loads(process.stdout.readline())
        self.assertEqual(event['relation'], 'E2')
        send({'status': 'returned', 'fresh_id': 0,
              'outputs': [{'position': 0,
                           'value': {'type': 'nat', 'value': 8}}]})
        result = json.loads(process.stdout.readline())
        code = process.wait(timeout=30)
        stderr = process.stderr.read()
        process.stdin.close()
        process.stdout.close()
        process.stderr.close()
        self.assertEqual(code, 0, stderr)
        self.assertEqual(result['status'], 'passed')
        self.assertEqual(result['pre_outputs'], [{'type': 'nat', 'value': '8'}])


if __name__ == '__main__':
    unittest.main()
