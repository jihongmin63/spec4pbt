"""The two passes consume the same Input in separate evidence runs."""
from pathlib import Path
import json
import subprocess
import sys
import tempfile
import unittest

from scripts.property.cli import fixed_hashes, read_inputs


ROOT = Path(__file__).resolve().parents[2]
DEMO = ROOT / 'properties/property_replay_demo'
INPUT = json.dumps({'x': {'type': 'nat', 'value': '7'}})


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
