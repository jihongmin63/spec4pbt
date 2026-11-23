"""Real Coq integration tests: reject broken chains and execute a selected candidate."""
import json
from pathlib import Path
import subprocess
import shutil
import sys
import tempfile
import unittest
import importlib.util

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from check import CheckError, Session, assumptions, validate_source
import run as runner


class WorkflowTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems')
        self.addCleanup(self.temp.cleanup)
        self.prop = Path(self.temp.name)
        (self.prop / 'Original.v').write_text('''From QuickChick Require Import QuickChick.
Definition Input := nat.
Definition encode_input (x : Input) : string := show x.
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

    def test_tactic_extracts_from_actual_translated_relation(self):
        """Catch Outcome universe errors in the fork's tactic on emitted AL code."""
        driver_spec = importlib.util.spec_from_file_location('translate_for_property_test',
                                                              ROOT / 'scripts/translate.py')
        driver = importlib.util.module_from_spec(driver_spec)
        driver_spec.loader.exec_module(driver)
        run = Path(tempfile.mkdtemp(prefix='property-tactic.',
                                    dir=ROOT / '_opam-testing-theorems/checks'))
        frontend, _ = driver.prepare_backend(
            ROOT / '_opam-testing-theorems/sources/p4-spectec', run)
        build = subprocess.run(['bash', str(ROOT / 'environment/env.sh'), 'frontend',
                                'dune', 'build', '--root', str(frontend), '-j', '2',
                                'p4spec/al_to_coq/main.exe'], capture_output=True,
                               text=True, timeout=240)
        (run / 'backend.log').write_text(build.stdout + build.stderr)
        self.assertEqual(build.returncode, 0, build.stdout + build.stderr)
        executable = frontend / '_build/default/p4spec/al_to_coq/main.exe'
        source = run / 'spec'
        generated = subprocess.run(['bash', str(ROOT / 'environment/env.sh'), 'frontend',
                                    str(executable), '--profile', 'fixture', '--input',
                                    str(ROOT / 'translator/tests/inductive/simple.watsup'),
                                    '--output', str(source), '--manifest',
                                    str(run / 'manifest.json')], capture_output=True,
                                   text=True, timeout=120)
        (run / 'generation.log').write_text(generated.stdout + generated.stderr)
        self.assertEqual(generated.returncode, 0, generated.stdout + generated.stderr)
        driver.compile_generated(source, 'fixture', run, {'commands': []})
        probe = run / 'Probe.v'
        probe.write_text('''From QuickChick Require Import QuickChick.
From Coq Require Import Arith List Bool.
From ALCoq Require Import Execution.
From FixtureSpec.Generated Require Import InductiveRelations_0000.
Import ListNotations QcDefaultNotation.
Open Scope qc_scope.
Require Extraction.
Record Input := mkInput { input_x : nat }.
#[global] Instance inputShow : Show Input := {| show := fun i => show (input_x i) |}.
Inductive predicate : Input -> Prop :=
| precondition : forall x y final,
    g_fixture_rel_Identity_execute x {| next_fresh := 0 |} (Success y) final ->
    predicate (mkInput x).
Definition encode_input (i : Input) : nat := input_x i.
Theorem generator_factory : forall x : Input, predicate x -> true = true.
Proof.
  quickchick 2.
  Extraction "generator.ml" GenSizedSuchThat_predicate_O encode_input.
  intros; reflexivity.
Qed.
Print Assumptions generator_factory.
''')
        command = ['bash', str(ROOT / 'environment/env.sh'), 'coqc', '-q',
                   '-Q', str(run / 'support'), 'ALCoq', '-Q', str(source),
                   'FixtureSpec', str(probe)]
        result = subprocess.run(command, cwd=run, capture_output=True,
                                text=True, timeout=120)
        (run / 'Probe.log').write_text(result.stdout + result.stderr)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertTrue((run / 'generator.ml').is_file())
        self.assertIn('Closed under the global context', result.stdout)
        prop = run / 'property'
        (prop / 'candidates/v001').mkdir(parents=True)
        (prop / 'Original.v').write_text('''From QuickChick Require Import QuickChick.
From ALCoq Require Import Execution.
From FixtureSpec.Generated Require Import InductiveRelations_0000.
Record Input := mkInput { input_x : nat }.
#[global] Instance inputShow : Show Input := {| show := fun i => show (input_x i) |}.
Inductive predicate : Input -> Prop :=
| precondition : forall x y final,
    g_fixture_rel_Identity_execute x {| next_fresh := 0 |} (Success y) final ->
    predicate (mkInput x).
Definition encode_input (i : Input) : string := show (input_x i).
''')
        (prop / 'candidates/v001/Candidate.v').write_text('''Require Property.Original.
Definition predicate := Property.Original.predicate.
''')
        (prop / 'candidates/v001/Equivalence.v').write_text('''Require Property.Original Property.candidates.v001.Candidate.
Theorem equivalent : forall x, Property.Original.predicate x <->
 Property.candidates.v001.Candidate.predicate x.
Proof. intros x; split; trivial. Qed.
''')
        session = Session(prop, fixture_root=source)
        session.check()
        self.assertIn('support/Execution.v', session.report['source_hashes'])
        self.assertIn('fixture/Generated/InductiveRelations_0000.v', session.report['source_hashes'])
        self.assertFalse(any(p.startswith('p4/') or p.startswith('wasm/')
                             for p in session.report['source_hashes']))

    def test_record_input_candidate_derives_from_translated_relations(self):
        """The fork's tactic needs the selected predicate in its own module."""
        property_dir = ROOT / 'properties/property_replay_demo'
        result = subprocess.run(
            [sys.executable, str(ROOT / 'scripts/run.py'), str(property_dir),
             '--candidate', 'v001', '--derive-only'], cwd=ROOT,
            capture_output=True, text=True, timeout=240)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        reports = sorted((property_dir / '.runs').glob('run-*/result.json'),
                         key=lambda p: p.stat().st_mtime_ns)
        report = json.loads(reports[-1].read_text())
        self.assertEqual(report['status'], 'passed')
        self.assertEqual(report['generator_factory_assumptions'], [])
        derived = (reports[-1].parent / 'sources/Derived.v').read_text()
        self.assertIn('Inductive predicate_v001', derived)
        self.assertIn('g_fixture_rel_B_execute', derived)

    def test_derive_only_selects_later_candidate_without_running_samples(self):
        result, run = self.invoke('run.py', '--candidate', 'v002', '--derive-only')
        self.assertEqual(result['status'], 'passed')
        self.assertEqual(result['sequence'], ['v001', 'v002'])
        self.assertTrue(result['derive_only'])
        self.assertTrue((run / 'sources/Derived.v').exists())
        self.assertFalse((run / 'samples.json').exists())
        self.assertFalse(any(command['log'] == 'execution.log' for command in result['commands']))

    def test_delegating_candidate_samples_predecessor_values(self):
        path = self.prop / 'candidates/v002'
        (path / 'Candidate.v').write_text('''Require Import Property.candidates.v001.Candidate.
Inductive predicate : Original.Input -> Prop :=
| forwarded : forall x, Property.candidates.v001.Candidate.predicate x -> predicate x.
''')
        (path / 'Equivalence.v').write_text('''Require Property.candidates.v001.Candidate Property.candidates.v002.Candidate.
Theorem equivalent : forall x, Property.candidates.v001.Candidate.predicate x <->
 Property.candidates.v002.Candidate.predicate x.
Proof.
  intro x; split; intro H.
  - constructor; exact H.
  - inversion H; subst; assumption.
Qed.
''')
        result, run = self.invoke('run.py', '--candidate', 'v002', '--samples', '8', '--size', '10')
        self.assertEqual(result['status'], 'passed')
        values = json.loads((run / 'samples.json').read_text())
        self.assertEqual(len(values), 8)
        self.assertTrue(all(v is None or isinstance(v, int) and v % 2 == 0 for v in values))
        self.assertIn('predicate_v002', (run / 'sources/Derived.v').read_text())

    def test_rejects_global_constant_in_candidate_premise(self):
        (self.prop / 'Original.v').write_text('''From QuickChick Require Import QuickChick.
Definition Input := nat.
Definition encode_input (x : Input) : string := show x.
Definition local_zero : nat := 0.
Inductive predicate : Input -> Prop :=
| precondition : forall n, n = local_zero -> predicate n.
''')
        path = self.prop / 'candidates/v001'
        (path / 'Candidate.v').write_text('''Require Property.Original.
Definition local_zero : nat := 0.
Inductive predicate : Original.Input -> Prop :=
| precondition : forall n, n = local_zero -> predicate n.
''')
        (path / 'Equivalence.v').write_text('''Require Property.Original Property.candidates.v001.Candidate.
Theorem equivalent : forall x, Property.Original.predicate x <->
 Property.candidates.v001.Candidate.predicate x.
Proof. intro x; split; intro H; induction H; constructor; assumption. Qed.
''')
        result, _ = self.invoke('run.py', '--candidate', 'v001', '--derive-only', success=False)
        self.assertIn('global constant', result['error'].lower())

    def test_rejects_unaliased_standard_function_in_premise(self):
        (self.prop / 'Original.v').write_text('''From QuickChick Require Import QuickChick.
Definition Input := nat.
Definition encode_input (x : Input) : string := show x.
Inductive predicate : Input -> Prop :=
| precondition : forall n, Nat.eqb n 0 = true -> predicate n.
''')
        path = self.prop / 'candidates/v001'
        (path / 'Candidate.v').write_text('''Require Property.Original.
Inductive predicate : Original.Input -> Prop :=
| precondition : forall n, Nat.eqb n 0 = true -> predicate n.
''')
        (path / 'Equivalence.v').write_text('''Require Property.Original Property.candidates.v001.Candidate.
Theorem equivalent : forall x, Property.Original.predicate x <->
 Property.candidates.v001.Candidate.predicate x.
Proof. intro x; split; intro H; induction H; constructor; assumption. Qed.
''')
        result, _ = self.invoke('run.py', '--candidate', 'v001', '--derive-only', success=False)
        self.assertIn('unaliased standard function', result['error'].lower())

    def test_rejects_function_call_in_constructor_conclusion(self):
        (self.prop / 'Original.v').write_text('''From QuickChick Require Import QuickChick.
Definition Input := nat.
Definition encode_input (x : Input) : string := show x.
Inductive predicate : Input -> Prop :=
| precondition : forall n, predicate (Nat.add n 1).
''')
        path = self.prop / 'candidates/v001'
        (path / 'Candidate.v').write_text('''Require Property.Original.
Inductive predicate : Original.Input -> Prop :=
| precondition : forall n, predicate (Nat.add n 1).
''')
        (path / 'Equivalence.v').write_text('''Require Property.Original Property.candidates.v001.Candidate.
Theorem equivalent : forall x, Property.Original.predicate x <->
 Property.candidates.v001.Candidate.predicate x.
Proof.
  intro x; split; intro H.
  - destruct H as [n]; constructor.
  - destruct H as [n]; constructor.
Qed.
''')
        result, _ = self.invoke('run.py', '--candidate', 'v001', '--derive-only', success=False)
        self.assertIn('function call', result['error'].lower())

    def test_allows_quickchick_import_but_blocks_extraction_override(self):
        validate_source(Path('Original.v'), b'From QuickChick Require Import QuickChick.\n')
        with self.assertRaises(CheckError):
            validate_source(Path('Candidate.v'), b'Extract Constant predicate => "true".\n')

    def test_authored_axioms_are_rejected_but_support_context_is_accepted(self):
        with self.assertRaisesRegex(CheckError, 'Axiom'):
            validate_source(Path('Original.v'), b'Axiom unsound : False.\n')
        validate_source(Path('Execution.v'), b'Section Evaluation. Context {A : Type}. End Evaluation.\n',
                        authored=False)

    def test_compiles_only_selected_support_closure(self):
        original = self.prop / 'Original.v'
        original.write_text('From ALCoq Require Import Execution.\n' + original.read_text())
        result, run = self.invoke('check.py')
        self.assertEqual(result['status'], 'passed')
        self.assertIn('support/Execution.v', result['source_hashes'])
        self.assertFalse(any(p.startswith('p4/') or p.startswith('wasm/')
                             for p in result['source_hashes']))

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
        self.assertIn('admitted', result['error'].lower())

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
        self.assertEqual(result['samples'], 12)
        values = json.loads((run / 'samples.json').read_text())
        self.assertEqual(len(values), 12)
        self.assertTrue(all(value is not None and isinstance(value, int) and value % 2 == 0 for value in values))
        self.assertTrue((run / 'sources/Derived.v').exists())
        self.assertFalse((self.prop / 'candidates/v001/Generator.v').exists())
        rerun = subprocess.run([str(run / 'sources/sampler')], capture_output=True, text=True, check=True)
        self.assertEqual(json.loads(rerun.stdout), values)


if __name__ == '__main__':
    unittest.main()
