"""Real Coq integration tests: reject broken chains and execute a selected candidate."""
import json
from pathlib import Path
import subprocess
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from check import CheckError, Session, assumptions, validate_source
import run as runner


class WorkflowTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems')
        self.addCleanup(self.temp.cleanup)
        self.prop = Path(self.temp.name)
        (self.prop / 'Original.v').write_text('''Definition Input := nat.
Inductive predicate : Input -> Prop :=
| zero : predicate 0
| step : forall n, predicate n -> predicate (S (S n)).
''')
        self.candidate('v001', 'Property.Original')
        self.candidate('v002', 'Property.candidates.v001.Candidate')

    def candidate(self, name, previous):
        path = self.prop / 'candidates' / name
        path.mkdir(parents=True)
        (path / 'Candidate.v').write_text('''Require Import Property.Original.
Inductive predicate : Original.Input -> Prop :=
| zero : predicate 0
| step : forall n, predicate n -> predicate (S (S n)).
''')
        (path / 'Equivalence.v').write_text(f'''Require {previous} Property.candidates.{name}.Candidate.
Theorem equivalent : forall x,
  {previous}.predicate x <-> Property.candidates.{name}.Candidate.predicate x.
Proof.
  intro x; split; intro H; induction H; constructor; assumption.
Qed.
''')

    def invoke(self, script, *args, success=True):
        process = subprocess.run([sys.executable, str(ROOT / 'scripts' / script),
                                  str(self.prop), *args], cwd=ROOT,
                                 capture_output=True, text=True, timeout=240)
        self.assertEqual(process.returncode == 0, success, process.stdout + process.stderr)
        reports = sorted((self.prop / '.runs').glob('*/result.json'), key=lambda p: p.stat().st_mtime_ns)
        self.assertTrue(reports, process.stdout + process.stderr)
        return json.loads(reports[-1].read_text()), reports[-1].parent

    def test_audit_never_ignores_unicode_or_malformed_assumptions(self):
        found = assumptions('Axioms:\nRandomQC.RandomSeed : Type\nProperty.Original.α : False\n')
        self.assertIn('Property.Original.α', found)
        with self.assertRaises(CheckError):
            assumptions('Axioms:\nRandomQC.RandomSeed : Type\nunrecognized grouped assumptions : Type\n')

    def test_derive_only_selects_later_candidate_without_running_samples(self):
        result, run = self.invoke('run.py', '--candidate', 'v002', '--derive-only')
        self.assertEqual(result['status'], 'passed')
        self.assertEqual(result['sequence'], ['v001', 'v002'])
        self.assertTrue(result['derive_only'])
        self.assertTrue((run / 'sources/Derived.v').exists())
        self.assertFalse((run / 'samples.json').exists())
        self.assertFalse(any(command['log'] == 'execution.log' for command in result['commands']))

    def test_allows_quickchick_import_but_blocks_extraction_override(self):
        validate_source(Path('Original.v'), b'From QuickChick Require Import QuickChick.\n')
        with self.assertRaises(CheckError):
            validate_source(Path('Candidate.v'), b'Extract Constant predicate => "true".\n')

    def test_records_the_pinned_opam_packages(self):
        # The real property workspace is outside the local opam switch directory.
        with tempfile.TemporaryDirectory(dir=ROOT / 'properties') as outside:
            shutil.copytree(self.prop, outside, dirs_exist_ok=True)
            session = Session(Path(outside))
            session.snapshot()
            packages = (session.directory / 'packages.log').read_text()
        self.assertRegex(packages, r'(?m)^coq\s+8\.20\.0\s*$')
        self.assertRegex(packages, r'(?m)^coq-quickchick\s+dev\s*$')

    def test_compiles_integer_alias_in_extracted_implementation_and_interface(self):
        normalize = getattr(runner, 'normalize_extraction', None)
        self.assertTrue(callable(normalize), 'Generated .ml and .mli need the same integer alias normalization')
        (self.prop / 'samples.ml').write_text('type int = int\nlet answer : int = 7\n')
        (self.prop / 'samples.mli').write_text('type int = int\nval answer : int\n')
        normalize(self.prop)
        for args in [('ocamlopt', '-c', 'samples.mli'), ('ocamlopt', '-c', 'samples.ml')]:
            compiled = subprocess.run(['bash', str(ROOT / 'environment/env.sh'), *args],
                                      cwd=self.prop, capture_output=True, text=True, timeout=30)
            self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)

    def test_stops_on_timeout(self):
        session = Session(self.prop, timeout=0.1)
        with self.assertRaisesRegex(CheckError, 'timed out'):
            session.command([sys.executable, '-c', 'import time; time.sleep(10)'], 'slow', coq=False)
        self.assertEqual(session.report['commands'][-1]['status'], 'timeout')

    def test_rejects_sequence_change_after_snapshot(self):
        session = Session(self.prop)
        session.snapshot()
        self.candidate('v003', 'Property.candidates.v002.Candidate')
        with self.assertRaisesRegex(CheckError, 'sequence changed'):
            session.fresh()

    def test_rejects_source_change_after_snapshot(self):
        session = Session(self.prop)
        session.snapshot()
        with (self.prop / 'Original.v').open('a') as stream:
            stream.write('\n(* changed *)\n')
        with self.assertRaisesRegex(CheckError, 'Source changed'):
            session.fresh()

    def test_run_refuses_a_broken_previous_link(self):
        p = self.prop / 'candidates/v001/Equivalence.v'
        p.write_text(p.read_text().split('Proof.')[0] + 'Admitted.\n')
        result, run = self.invoke('run.py', '--candidate', 'v002', success=False)
        self.assertEqual(result['status'], 'failed')
        self.assertFalse((run / 'sources/Derived.v').exists())

    def test_checks_every_link_without_deriving_generators(self):
        # A definition alias is fine for equivalence even if derivation needs an inductive.
        path = self.prop / 'candidates/v002'
        (path / 'Candidate.v').write_text('''Require Property.candidates.v001.Candidate.
Definition predicate := Property.candidates.v001.Candidate.predicate.
''')
        (path / 'Equivalence.v').write_text('''Require Property.candidates.v001.Candidate Property.candidates.v002.Candidate.
Theorem equivalent : forall x, Property.candidates.v001.Candidate.predicate x <->
 Property.candidates.v002.Candidate.predicate x.
Proof. intro x; split; trivial. Qed.
''')
        result, run = self.invoke('check.py')
        self.assertEqual(result['status'], 'passed')
        self.assertEqual(result['sequence'], ['v001', 'v002'])
        self.assertEqual(result['assumptions'], [])
        self.assertFalse((run / 'sources/Derived.v').exists())

    def test_rejects_wrong_middle_link_even_when_later_link_is_valid(self):
        (self.prop / 'candidates/v001/Equivalence.v').write_text('''Require Property.Original.
Theorem equivalent : forall x, Property.Original.predicate x <-> Property.Original.predicate x.
Proof. intro x; split; trivial. Qed.
''')
        result, _ = self.invoke('check.py', success=False)
        self.assertEqual(result['status'], 'failed')

    def test_rejects_admitted_equivalence(self):
        p = self.prop / 'candidates/v001/Equivalence.v'
        p.write_text(p.read_text().split('Proof.')[0] + 'Admitted.\n')
        result, _ = self.invoke('check.py', success=False)
        self.assertIn('assumption', result['error'].lower())

    def test_rejects_missing_step(self):
        (self.prop / 'candidates/v002').rename(self.prop / 'candidates/v003')
        process = subprocess.run([sys.executable, str(ROOT / 'scripts/check.py'), str(self.prop)],
                                 cwd=ROOT, capture_output=True, text=True)
        self.assertNotEqual(process.returncode, 0)
        self.assertIn('sequence', process.stderr.lower())

    def test_runs_selected_candidate_without_requiring_later_candidate(self):
        (self.prop / 'candidates/v002/Equivalence.v').write_text('This is unfinished.\n')
        result, run = self.invoke('run.py', '--candidate', 'v001', '--samples', '12', '--size', '8', '--seed', '7')
        self.assertEqual(result['status'], 'passed')
        self.assertEqual(result['sequence'], ['v001'])
        self.assertEqual(result['candidate'], 'v001')
        self.assertEqual(result['generator_proof'], 'not_checked')
        self.assertEqual(result['assumptions'], [])
        self.assertEqual(result['samples'], 12)
        values = json.loads((run / 'samples.json').read_text())
        self.assertEqual(len(values), 12)
        self.assertTrue(all(value is not None and int(value) % 2 == 0 for value in values))
        self.assertTrue((run / 'sources/Derived.v').exists())
        self.assertFalse((self.prop / 'candidates/v001/Generator.v').exists())
        rerun = subprocess.run([str(run / 'sources/sampler')], capture_output=True, text=True, check=True)
        self.assertEqual(json.loads(rerun.stdout), values)


if __name__ == '__main__':
    unittest.main()
