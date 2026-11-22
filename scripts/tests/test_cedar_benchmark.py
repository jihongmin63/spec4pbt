"""Real Coq regressions for the pinned full-property scheduler adapter."""
import json
import io
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
PROPERTY = ROOT / 'properties/cedar_no_type_error'
RUNS = PROPERTY / '.runs'
sys.path.insert(0, str(ROOT / 'scripts'))
from cedar.serialization import (_coq_literal, _split_top, reconstruct_candidate,
                                 SerializationError)
from cedar.benchmark import parse_quickchick_result
from cedar import benchmark

CANDIDATE = '''From Coq Require Import List.
Require Import Specification.cedar.Spec Property.Original.
Import ListNotations.
Inductive predicate : Original.Input -> Prop :=
| intro : forall ets acts rs e es ty expr,
    WfSchema Original.entity_names (MkSchema ets acts) ->
    ActionSchemaToRequestTypes acts [] rs ->
    SchemaToEnvironments (MkSchema ets acts) rs (e :: es) ->
    WfCedarType Original.entity_names ty ->
    HasType (somepaths []) e expr ty ->
    predicate (Original.mkInput ets acts rs e es ty expr).
'''

EQUIVALENCE = '''Require Import Property.candidates.v001.Candidate.
Theorem equivalent : forall x, Original.predicate x <-> Candidate.predicate x.
Proof.
  intros [ets acts rs e es ty expr]; simpl; split.
  - intros [Hs [Hr [He [Ht Hp]]]]. exact (Candidate.intro _ _ _ _ _ _ _ Hs Hr He Ht Hp).
  - intros H. inversion H; subst; repeat split; assumption.
Qed.
'''


class CedarBenchmarkTests(unittest.TestCase):
    def setUp(self):
        RUNS.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(dir=RUNS, prefix='test-benchmark-')
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)

    def invoke(self, prop, candidate, attempts=10):
        output = prop / '.runs' / 'benchmark'
        argv = [sys.executable, str(ROOT / 'scripts/cedar/benchmark.py'),
                str(prop), '--candidate', candidate, '--seed', '101',
                '--attempts', str(attempts), '--test-mode',
                '--output-dir', str(output)]
        done = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True,
                              timeout=240)
        details = done.stdout + done.stderr
        if (output / 'result.json').exists():
            details += (output / 'result.json').read_text()
        self.assertEqual(done.returncode, 0, details)
        return output, json.loads((output / 'result.json').read_text())

    def test_official_p0_scheduler_extracts_and_proves_seven_field_adapter(self):
        prop = self.base / 'property'
        prop.mkdir()
        shutil.copy2(PROPERTY / 'Original.v', prop / 'Original.v')
        output, result = self.invoke(prop, 'P0')
        scheduler = (output / 'scheduler.log').read_text()
        self.assertEqual(result['status'], 'completed')
        self.assertEqual(result['derivation']['status'], 'succeeded')
        self.assertEqual(result['quickchick'], parse_quickchick_result(scheduler))
        # With the literal entity list the internal run matches the upstream
        # artifact (10000 passed, about 2400 discards) instead of giving up.
        self.assertEqual(result['quickchick']['status'], 'passed')
        self.assertEqual(result['quickchick']['tests'], 10000)
        self.assertEqual(result['size'], 2)
        self.assertEqual(result['counts']['generated'] +
                         result['counts']['discard'], 10)
        self.assertIn('Theorem Schedule:', scheduler)
        self.assertIn('Pieces:', scheduler)
        self.assertIn('Closed under the global context', scheduler)
        self.assertIn('Closed under the global context',
                      (output / 'support.log').read_text())
        self.assertTrue((output / 'sources/theorem.ml').is_file())
        rows = [json.loads(line) for line in (output / 'attempts.jsonl').read_text().splitlines()]
        self.assertEqual([row['attempt'] for row in rows], list(range(10)))
        self.assertEqual(len(rows), 10)
        self.assertTrue(any(row['input_coq'] for row in rows))
        self.assertTrue((output / 'sources/Adapter0000.vo').is_file())
        self.assertTrue(all(row['scheduler_entity_names'] is None for row in rows))
        schedule = benchmark.schedule_text(scheduler)
        self.assertNotIn('entity_names', schedule)
        self.assertTrue(set(result['derivation_guards']['schedule_binders']) >=
                        {'ty', 'rs', 'expr'})
        self.assertIn('entity_names_literal', (output / 'sources/Bench.v').read_text())

    def test_checked_candidate_uses_same_official_tactic_and_counted_attempts(self):
        prop = self.base / 'candidate-property'
        candidate = prop / 'candidates/v001'
        candidate.mkdir(parents=True)
        shutil.copy2(PROPERTY / 'Original.v', prop / 'Original.v')
        (candidate / 'Candidate.v').write_text(CANDIDATE)
        (candidate / 'Equivalence.v').write_text(EQUIVALENCE)
        output, result = self.invoke(prop, 'v001')
        self.assertEqual(result['status'], 'completed')
        self.assertEqual(result['derivation']['status'], 'succeeded')
        self.assertEqual(result['quickchick'],
                         parse_quickchick_result((output / 'scheduler.log').read_text()))
        self.assertEqual(result['quickchick']['status'], 'passed')
        self.assertEqual(result['derivation_guards']['schedule_binders'], ['x'])
        self.assertEqual(result['derivation_guards']['reachable_relations'], ['predicate_v001'])
        rewrite = json.loads((output / 'derivation-rewrite.json').read_text())
        self.assertEqual(rewrite['versions']['v001']['declared'], ['predicate', 'intro'])
        copy = (output / 'sources/property/candidates/v001/Candidate.v').read_text()
        self.assertNotIn('entity_names', copy)
        self.assertIn('Inductive predicate_v001', copy)
        self.assertEqual((prop / 'candidates/v001/Candidate.v').read_text().count('predicate_v001'), 0)
        self.assertEqual(result['counts']['generated'] +
                         result['counts']['discard'], 10)
        self.assertTrue(result['prefix_check'])
        self.assertIn('Theorem Schedule:', (output / 'scheduler.log').read_text())
        self.assertTrue((output / 'sources/theorem.ml').is_file())
        self.assertEqual(len((output / 'attempts.jsonl').read_text().splitlines()), 10)

    def test_predecessor_relation_gets_its_own_generator(self):
        # Before version-unique names, the plugin compiled a premise naming
        # the predecessor's ``predicate`` as a recursive call to itself.
        prop = self.base / 'chain-property'
        (prop / 'candidates/v001').mkdir(parents=True)
        shutil.copy2(PROPERTY / 'Original.v', prop / 'Original.v')
        (prop / 'candidates/v001/Candidate.v').write_text(CANDIDATE)
        (prop / 'candidates/v001/Equivalence.v').write_text(EQUIVALENCE)
        (prop / 'candidates/v002').mkdir()
        (prop / 'candidates/v002/Candidate.v').write_text('''Require Import List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Inductive predicate : Original.Input -> Prop :=
| Previous : forall i, Property.candidates.v001.Candidate.predicate i -> predicate i.
''')
        (prop / 'candidates/v002/Equivalence.v').write_text('''Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v002.Candidate.
Theorem equivalent : forall x, Property.candidates.v001.Candidate.predicate x <->
  Property.candidates.v002.Candidate.predicate x.
Proof.
  intro x; split; intro H.
  - exact (Property.candidates.v002.Candidate.Previous x H).
  - inversion H; assumption.
Qed.
''')
        output, result = self.invoke(prop, 'v002')
        self.assertEqual(result['status'], 'completed')
        self.assertEqual(result['derivation_guards']['reachable_relations'],
                         ['predicate_v001', 'predicate_v002'])
        extracted = (output / 'sources/theorem.ml').read_text()
        self.assertIn('genSizedSuchThat_predicate_v001_O', extracted)
        self.assertGreater(result['counts']['generated'], 0)

    def test_derivation_guards_reject_generated_constants_and_missing_relations(self):
        log = ('Theorem Schedule:\ndo (entity_names : _, ty : CedarType) <-G (W entity_names ty) ;\n'
               ' (vacts_ets11_ : _) <-G (S vacts_ets11_)\n=> check conclusion: x\n')
        with self.assertRaisesRegex(RuntimeError, 'entity_names'):
            benchmark.check_derivation(self.base, 'P0', log, None)
        good = log.replace('entity_names : _, ', '')
        self.assertEqual(benchmark.check_derivation(self.base, 'P0', good, None)['status'], 'passed')
        (self.base / 'theorem.ml').write_text('let genSizedSuchThat_predicate_v002_O = 0\n')
        candidate_log = 'Theorem Schedule:\ndo (x : Input) <-G (p x)\n=> check conclusion: y\n'
        record = {'reachable_relations': ['predicate_v001', 'predicate_v002']}
        with self.assertRaisesRegex(RuntimeError, 'predicate_v001'):
            benchmark.check_derivation(self.base, 'v002', candidate_log, record)
        record['reachable_relations'] = ['predicate_v002']
        self.assertEqual(benchmark.check_derivation(self.base, 'v002', candidate_log, record)
                         ['reachable_relations'], ['predicate_v002'])

    def test_quickchick_parser_records_reported_outcomes_and_rejects_ambiguity(self):
        gave_up = parse_quickchick_result('Theorem Schedule:\nPieces:\n'
                                           '*** Gave up! Passed only 3500 tests\n'
                                           'Discarded: 20000\nTime Elapsed: 2s\n')
        self.assertEqual(gave_up, {'status': 'gave_up', 'tests': 3500,
                                   'discards': 20000,
                                   'summary': '*** Gave up! Passed only 3500 tests\nDiscarded: 20000',
                                   'log': 'scheduler.log'})
        self.assertEqual(parse_quickchick_result('+++ Passed 10000 tests (2386 discards)\n'),
                         {'status': 'passed', 'tests': 10000, 'discards': 2386,
                          'summary': '+++ Passed 10000 tests (2386 discards)',
                          'log': 'scheduler.log'})
        failed = parse_quickchick_result('*** Failed after 6 tests and 0 shrinks. (0 discards)\n')
        self.assertEqual(failed['status'], 'failed')
        self.assertEqual(failed['tests'], 6)
        self.assertEqual(failed['discards'], 0)
        with self.assertRaisesRegex(RuntimeError, 'unrecognized'):
            parse_quickchick_result('Theorem Schedule:\nPieces:\n')
        with self.assertRaisesRegex(RuntimeError, 'ambiguous'):
            parse_quickchick_result('+++ Passed 1 tests (0 discards)\n'
                                     '*** Gave up! Passed only 0 tests\nDiscarded: 1\n')
        with self.assertRaisesRegex(RuntimeError, 'ambiguous'):
            parse_quickchick_result('+++ Passed 1 tests (0 discards)\n'
                                     '*** Gave up! Malformed summary\n')

    def test_later_compile_failure_keeps_actual_internal_outcome(self):
        prop = self.base / 'late-failure-property'
        prop.mkdir()
        shutil.copy2(PROPERTY / 'Original.v', prop / 'Original.v')
        output = prop / '.runs/benchmark'

        def fail_after_scheduler(_sources, _candidate, destination, _sequence=()):
            (destination / 'scheduler.log').write_text(
                'Theorem Schedule:\nPieces:\n'
                '*** Gave up! Passed only 4 tests\nDiscarded: 20\n')
            raise RuntimeError('later compile failed')

        argv = ['benchmark.py', str(prop), '--candidate', 'P0', '--seed', '101',
                '--attempts', '10', '--test-mode', '--output-dir', str(output)]
        with mock.patch.object(sys, 'argv', argv), \
             mock.patch.object(benchmark, 'snapshot', return_value=(prop, None, None, [])), \
             mock.patch.object(benchmark, 'compile_source', side_effect=fail_after_scheduler), \
             redirect_stdout(io.StringIO()):
            self.assertEqual(benchmark.main(), 1)
        result = json.loads((output / 'result.json').read_text())
        self.assertEqual(result['status'], 'failed')
        self.assertEqual(result['quickchick']['status'], 'gave_up')
        self.assertEqual(result['quickchick']['tests'], 4)
        self.assertEqual(result['quickchick']['discards'], 20)
        self.assertIn('later compile failed', result['error'])

    def test_full_candidate_payload_parses_and_coq_checks_nested_fields(self):
        # This callback shape is produced by ShowInput.  A nonempty request
        # list, environment tail, attributes, path list, quote and negative Z
        # catch lossy or syntactically ambiguous transport.
        name = r'MkName "A;B (C) \"D\"" []'
        entry = 'MkEntitySchemaEntry [] [(("attr", true), intType)]'
        schema = f'MkSchema [({name}, {entry})] []'
        request = (f'MkRequest ({name}) (MkEntityUID ({name}) "action") ({name}) '
                   '[( ("requested", false), stringType)]')
        environment = f'MkEnvironment ({schema}) ({request})'
        display = (f'Original.mkInput ([({name}, {entry})]) ([]) '
                   f'([{request}]) ({environment}) ([{environment}]) '
                   '(intType) ((lit (int -1), somepaths [lit (int 0)]))')
        term = reconstruct_candidate([display + '\n'])
        self.assertIn('int (-1)%Z', term)
        source = self.base / 'CandidateTransport.v'
        source.write_text('''From Coq Require Import List String ZArith.
Require Import Specification.cedar.Spec Property.Original.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Definition received : Original.Input := ''' + term + '''.
Example full_fields : Original.es received <> [] /\\ Original.rs received <> [] /\\
  Original.expr received = (lit (int (-1)%Z), somepaths [lit (int 0)]).
Proof. repeat split; discriminate || reflexivity. Qed.
''')
        # Compile in a fresh snapshot with the same real Spec/Original modules.
        work = self.base / 'coq'
        (work / 'specification/cedar').mkdir(parents=True)
        (work / 'property').mkdir()
        shutil.copy2(ROOT / 'specification/cedar/Spec.v',
                     work / 'specification/cedar/Spec.v')
        shutil.copy2(PROPERTY / 'Original.v', work / 'property/Original.v')
        shutil.copy2(source, work / 'CandidateTransport.v')
        flags = ['-q', '-R', 'specification', 'Specification', '-R', 'property', 'Property']
        for file in ('specification/cedar/Spec.v', 'property/Original.v',
                     'CandidateTransport.v'):
            done = subprocess.run(['bash', str(ROOT / 'environment/env.sh'),
                                   'coqc', *flags, file], cwd=work,
                                  capture_output=True, text=True, timeout=60)
            self.assertEqual(done.returncode, 0, done.stdout + done.stderr)

    def test_lexical_transport_rejects_unbalanced_and_preserves_escaped_strings(self):
        self.assertEqual(_coq_literal(r'"quoted \"-3\"" int -10'),
                         r'"quoted ""-3""" int (-10)%Z')
        escaped = _coq_literal(r'"tab\t slash\\ octal\001"')
        self.assertIn('Ascii.ascii_of_nat 9', escaped)
        self.assertIn('Ascii.ascii_of_nat 92', escaped)
        self.assertIn('Ascii.ascii_of_nat 1', escaped)
        self.assertEqual(_split_top(r'(foo "x;y"), [bar; baz]', ','),
                         [r'(foo "x;y")', '[bar; baz]'])
        self.assertEqual(_coq_literal(r'"trailing\\"'), r'"trailing\"')
        self.assertEqual(_split_top(r'("trailing\"), [bar; baz]', ','),
                         [r'("trailing\")', '[bar; baz]'])
        with self.assertRaises(SerializationError):
            _split_top('MkSchema [(', ' ')
        with self.assertRaises(SerializationError):
            reconstruct_candidate(['Original.mkInput ([]) ([])\n'])


if __name__ == '__main__':
    unittest.main()
