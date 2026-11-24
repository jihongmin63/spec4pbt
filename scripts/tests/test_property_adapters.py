"""Subprocess JSON-lines adapter validates every observed slot and fresh_id."""
from pathlib import Path
import sys
import tempfile
import time
import unittest

from scripts.property.adapters import AdapterProtocolError, AdapterSession, AdapterTimeout
from scripts.property.compiler import compile_replay, compile_spec


ROOT = Path(__file__).resolve().parents[2]
DEMO = ROOT / 'properties/property_replay_demo'
SPEC = ROOT / 'specification/property_replay_demo/source/Property.watsup'


class AdapterTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.program = compile_replay(compile_spec(SPEC, DEMO / 'Property.toml'))

    def session(self, script, timeout=2):
        return AdapterSession(self.program,
                              {'demo_external': [sys.executable, str(script)]},
                              timeout=timeout)

    def test_demo_returns_actual_typed_value_and_counter(self):
        script = ROOT / 'adapters/property_replay_demo/demo_external.py'
        with self.session(script) as session:
            result = session.call('External',
                                  [{'type': 'nat', 'value': '7'}], 4)
        self.assertEqual(result['outputs'], [
            {'position': 0, 'value': {'type': 'nat', 'value': '20'}}])
        self.assertEqual(result['fresh_id'], 4)
        self.assertEqual(session.call_count, 1)

    def test_missing_fresh_and_wrong_slot_are_protocol_errors(self):
        for response in (
            '{"status":"returned","outputs":[{"position":0,"value":{"type":"nat","value":"20"}}]}',
            '{"status":"returned","fresh_id":0,"outputs":[{"position":1,"value":{"type":"nat","value":"20"}}]}',
            '{"status":"returned","fresh_id":0,"outputs":[{"position":0.0,"value":{"type":"nat","value":"20"}}]}',
            '{"status":"returned","fresh_id":0,"outputs":[{"position":false,"value":{"type":"nat","value":"20"}}]}',
        ):
            with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
                script = Path(temp) / 'bad.py'
                script.write_text('import sys\nfor line in sys.stdin:\n print(' + repr(response) + ', flush=True)\n')
                with self.session(script) as session:
                    with self.assertRaises(AdapterProtocolError):
                        session.call('External', [{'type': 'nat', 'value': '7'}], 0)

    def test_timeout_is_not_no_match(self):
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            script = Path(temp) / 'slow.py'
            script.write_text('import sys,time\nfor line in sys.stdin:\n time.sleep(3)\n')
            with self.session(script, timeout=0.1) as session:
                with self.assertRaises(AdapterTimeout):
                    session.call('External', [{'type': 'nat', 'value': '7'}], 0)

    def test_each_call_has_fresh_adapter_process(self):
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            script = Path(temp) / 'counter.py'
            script.write_text('import json,sys\ncount=0\nfor line in sys.stdin:\n'
                              ' count+=1\n request=json.loads(line)\n'
                              ' print(json.dumps({"status":"returned","fresh_id":request["fresh_id"],'
                              '"outputs":[{"position":0,"value":{"type":"nat","value":str(count)}}]}),flush=True)\n')
            with self.session(script) as session:
                values = [session.call('External',
                                       [{'type': 'nat', 'value': '7'}], fresh)
                          for fresh in (0, 1)]
        self.assertEqual([value['outputs'][0]['value']['value'] for value in values],
                         ['1', '1'])
        self.assertEqual([value['fresh_id'] for value in values], [0, 1])

    def test_partial_json_line_still_obeys_timeout(self):
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            script = Path(temp) / 'partial.py'
            script.write_text(
                'import sys,time\n'
                'sys.stdin.readline()\n'
                'sys.stdout.write(\'{"status":\'); sys.stdout.flush()\n'
                'time.sleep(0.7)\n'
                'print(\'"no_match","fresh_id":0}\',flush=True)\n')
            started = time.monotonic()
            with self.session(script, timeout=0.2) as session:
                with self.assertRaises(AdapterTimeout):
                    session.call('External', [{'type': 'nat', 'value': '7'}], 0)
            self.assertLess(time.monotonic() - started, 0.5)

    def test_callbacks_share_one_input_deadline(self):
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            script = Path(temp) / 'delayed.py'
            script.write_text(
                'import sys,time\n'
                'sys.stdin.readline()\n'
                'time.sleep(0.3)\n'
                'print(\'{"status":"no_match","fresh_id":0}\',flush=True)\n')
            started = time.monotonic()
            with self.session(script, timeout=0.45) as session:
                self.assertEqual(session.call('External',
                    [{'type': 'nat', 'value': '7'}], 0)['status'], 'no_match')
                with self.assertRaises(AdapterTimeout):
                    session.call('External', [{'type': 'nat', 'value': '7'}], 0)
            self.assertLess(time.monotonic() - started, 0.6)

    def test_request_write_obeys_deadline_when_adapter_does_not_read(self):
        from types import SimpleNamespace
        model = SimpleNamespace(
            type_schema={},
            external=[{'relation': 'E', 'adapter': 'test', 'observed_outputs': []}],
            definitions=[{'name': 'E', 'input_types': ['text'], 'output_types': []}])
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            script = Path(temp) / 'blocked.py'
            script.write_text('import time\ntime.sleep(0.7)\n')
            started = time.monotonic()
            with AdapterSession(SimpleNamespace(model=model),
                    {'test': [sys.executable, str(script)]}, timeout=0.2) as session:
                with self.assertRaises(AdapterTimeout):
                    session.call('E', [{'type': 'text', 'value': 'x' * 1000000}], 0)
            self.assertLess(time.monotonic() - started, 0.5)


if __name__ == '__main__':
    unittest.main()
