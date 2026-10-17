"""Direct P4-SpecTec translation feeds certified checks of actual observations."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

from pbt.run_observable import RunOptions, run_observable

ROOT = Path(__file__).resolve().parents[1]


def options(output, mode):
    return RunOptions(
        manifest=ROOT / 'specifications/p4record/Generated/manifest.json',
        config=ROOT / 'specifications/p4record/observations.toml', observation_id='value',
        spec_module='specifications.p4record.Generated.Transport',
        view_module='pbt.p4record.View', view_namespace='P4View',
        property_module='pbt.p4record.Property', premise='P4Property.Premise',
        target='P4Property.Target', check='P4Property.check', check_correct='P4Property.check_correct',
        generator_module='pbt.p4record.Generator', generator='P4Property.correctGenerator',
        adapter=(sys.executable, str(ROOT / 'pbt/p4record/adapter.py'), mode),
        output=output, count=4, size=5, seed=0)


class P4ExampleTests(unittest.TestCase):
    def test_hidden_state_changes_pass_and_observed_violation_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            for mode, expected in [('correct', 'passed'), ('hidden-change', 'passed'), ('wrong', 'failed')]:
                result = run_observable(ROOT, options(base / mode, mode))
                self.assertEqual(result.status, expected, result.error)
            normal = json.loads((base / 'correct/case-000000/process.json').read_text())
            changed = json.loads((base / 'hidden-change/case-000000/process.json').read_text())
            self.assertEqual(json.loads(normal['stderr'])['TRACE'], 0)
            self.assertEqual(json.loads(changed['stderr'])['TRACE'], -999)
            self.assertEqual(normal['stdout'], changed['stdout'])


if __name__ == '__main__':
    unittest.main()
