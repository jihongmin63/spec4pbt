"""Real JSON-lines subprocesses share an input's wall-clock deadline."""
from pathlib import Path
import tempfile
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch
import sys

from scripts.property.adapters import AdapterSession, AdapterTimeout
from scripts.property.bridge import ROOT
from scripts.property.engine import BridgeTimeout, run_bridge


class EngineTimeoutTests(unittest.TestCase):
    def script(self, directory, name, body):
        path = Path(directory) / name
        path.write_text('#!' + sys.executable + '\n' + body)
        path.chmod(0o700)
        return path

    def test_partial_bridge_line_does_not_block_after_readiness(self):
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            bridge = self.script(temp, 'bridge.py',
                'import sys,time\n'
                'sys.stdin.readline()\n'
                'sys.stdout.write(\'{"status":\'); sys.stdout.flush()\n'
                'time.sleep(0.7)\n'
                'print(\'"passed"}\',flush=True)\n')
            started = time.monotonic()
            with patch('scripts.property.engine.build_bridge', return_value=bridge):
                with self.assertRaises(BridgeTimeout):
                    run_bridge('debug', bridge, {}, timeout=0.2)
            self.assertLess(time.monotonic() - started, 0.5)

    def test_native_work_reduces_adapter_remaining_time(self):
        model = SimpleNamespace(
            type_schema={},
            external=[{'relation': 'E', 'adapter': 'test', 'observed_outputs': []}],
            definitions=[{'name': 'E', 'input_types': [], 'output_types': []}])
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            bridge = self.script(temp, 'bridge.py',
                'import sys,time\n'
                'sys.stdin.readline()\n'
                'time.sleep(0.15)\n'
                'print(\'{"kind":"external_call","relation":"E","input":[],"fresh_id":0}\',flush=True)\n'
                'sys.stdin.readline()\n'
                'print(\'{"status":"passed"}\',flush=True)\n')
            adapter = self.script(temp, 'adapter.py',
                'import sys,time\n'
                'sys.stdin.readline()\n'
                'time.sleep(0.7)\n'
                'print(\'{"status":"no_match","fresh_id":0}\',flush=True)\n')
            started = time.monotonic()
            with AdapterSession(SimpleNamespace(model=model),
                                {'test': [str(adapter)]}, timeout=5) as session:
                with patch('scripts.property.engine.build_bridge', return_value=bridge):
                    with self.assertRaises((BridgeTimeout, AdapterTimeout)):
                        run_bridge('replay', bridge, {}, timeout=0.4,
                            callback=lambda event: session.call(
                                event['relation'], event['input'], event['fresh_id']))
            self.assertLess(time.monotonic() - started, 0.65)

    def test_bridge_request_write_obeys_deadline_when_child_does_not_read(self):
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            bridge = self.script(temp, 'bridge.py', 'import time\ntime.sleep(0.7)\n')
            started = time.monotonic()
            with patch('scripts.property.engine.build_bridge', return_value=bridge):
                with self.assertRaises(BridgeTimeout):
                    run_bridge('debug', bridge, {'input': 'x' * 1000000}, timeout=0.2)
            self.assertLess(time.monotonic() - started, 0.5)


if __name__ == '__main__':
    unittest.main()
