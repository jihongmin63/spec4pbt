"""The demo uses translated relations and closed Coq equivalence proofs."""
from pathlib import Path
import json
import subprocess
import sys
import unittest

from scripts.property.rocq import render_original


ROOT = Path(__file__).resolve().parents[2]
DEMO = ROOT / 'properties/property_replay_demo'


class RocqTests(unittest.TestCase):
    def test_fixed_original_is_rendered_from_direct_spec_relations(self):
        generated = render_original(
            ROOT / 'specification/property_replay_demo/source/Property.watsup',
            DEMO / 'Property.toml')
        self.assertEqual(generated, (DEMO / 'Original.v').read_text())
        self.assertIn('g_fixture_rel_External_execute x {| next_fresh := 0 |}',
                      generated)
        self.assertIn('g_fixture_rel_B_execute b middle (Success c) final',
                      generated)
        self.assertNotIn('g_fixture_rel_Goal_execute', generated)

    def test_helper_pass_evidence_and_v002_tactic_derivation(self):
        for script, arguments in (
            ('check.py', []),
            ('run.py', ['--candidate', 'v002', '--derive-only']),
        ):
            process = subprocess.run(
                [sys.executable, str(ROOT / 'scripts' / script),
                 str(DEMO), *arguments], cwd=ROOT,
                capture_output=True, text=True, timeout=240)
            self.assertEqual(process.returncode, 0,
                             process.stdout + process.stderr)
            reports = sorted((DEMO / '.runs').glob(
                ('check-' if script == 'check.py' else 'run-') + '*/result.json'),
                key=lambda path: path.stat().st_mtime_ns)
            report = json.loads(reports[-1].read_text())
            self.assertEqual(report['status'], 'passed')
            self.assertIn('property/candidates/v002/Helper.watsup',
                          report['source_hashes'])
            self.assertIn('candidate/PassEvidence.json',
                          report['source_hashes'])
            self.assertIn('candidate/Generated/InductiveRelations_0000.v',
                          report['source_hashes'])
            if script == 'run.py':
                self.assertEqual(report['generator_factory_assumptions'], [])
                self.assertEqual(report['generator_proof'], 'not_checked')
                derived = (reports[-1].parent / 'sources/Derived.v').read_text()
                self.assertIn('g_candidate_rel_Helper_execute', derived)
                self.assertNotIn('g_fixture_rel_Goal_execute', derived)


if __name__ == '__main__':
    unittest.main()
