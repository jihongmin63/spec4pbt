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
        self.assertEqual(result['quickchick']['status'], 'gave_up')
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
        self.assertTrue(any(row['scheduler_entity_names'] !=
                            '[MkName "EntityType1" []; MkName "EntityType2" []]'
                            for row in rows if row['input_coq']))

    def test_checked_candidate_uses_same_official_tactic_and_counted_attempts(self):
        prop = self.base / 'candidate-property'
        candidate = prop / 'candidates/v001'
        candidate.mkdir(parents=True)
        shutil.copy2(PROPERTY / 'Original.v', prop / 'Original.v')
        (candidate / 'Candidate.v').write_text('''From Coq Require Import List.
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
''')
        (candidate / 'Equivalence.v').write_text('''Require Import Property.candidates.v001.Candidate.
Theorem equivalent : forall x, Original.predicate x <-> Candidate.predicate x.
Proof.
  intros [ets acts rs e es ty expr]; simpl; split.
  - intros [Hs [Hr [He [Ht Hp]]]]. exact (Candidate.intro _ _ _ _ _ _ _ Hs Hr He Ht Hp).
  - intros H. inversion H; subst; repeat split; assumption.
Qed.
''')
        output, result = self.invoke(prop, 'v001')
        self.assertEqual(result['status'], 'completed')
        self.assertEqual(result['derivation']['status'], 'succeeded')
        self.assertEqual(result['quickchick'],
                         parse_quickchick_result((output / 'scheduler.log').read_text()))
        self.assertEqual(result['quickchick']['status'], 'gave_up')
        self.assertEqual(result['counts']['generated'] +
                         result['counts']['discard'], 10)
        self.assertTrue(result['prefix_check'])
        self.assertIn('Theorem Schedule:', (output / 'scheduler.log').read_text())
        self.assertTrue((output / 'sources/theorem.ml').is_file())
        self.assertEqual(len((output / 'attempts.jsonl').read_text().splitlines()), 10)

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

        def fail_after_scheduler(_sources, _candidate, destination):
            (destination / 'scheduler.log').write_text(
                'Theorem Schedule:\nPieces:\n'
                '*** Gave up! Passed only 4 tests\nDiscarded: 20\n')
            raise RuntimeError('later compile failed')

        argv = ['benchmark.py', str(prop), '--candidate', 'P0', '--seed', '101',
                '--attempts', '10', '--test-mode', '--output-dir', str(output)]
        with mock.patch.object(sys, 'argv', argv), \
             mock.patch.object(benchmark, 'snapshot', return_value=(prop, None)), \
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
