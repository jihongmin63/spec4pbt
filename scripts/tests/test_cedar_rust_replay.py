"""Stored-input replay: actual syntax, budgets, and branch outcome accounting."""
import importlib.util
import unittest
import tempfile
import json
import os
from pathlib import Path


class ReplayTests(unittest.TestCase):
    def module(self):
        path = Path(__file__).resolve().parents[1] / 'cedar/rust_replay.py'
        self.assertTrue(path.exists(), 'stored-input replay adapter is missing')
        spec = importlib.util.spec_from_file_location('rust_replay', path)
        m = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(m)
        return m

    def test_constructor_strings_tuples_and_negative_integer(self):
        m = self.module()
        self.assertEqual(m.parse('(lit (int (-2)%Z), somepaths [])'),
                         (('lit', ('int', -2)), ('somepaths', [])))
        self.assertEqual(m.parse('"a""b"'), 'a"b')
        with self.assertRaises(ValueError):
            m.parse('lit (int 2) garbage')

    def test_structured_expression_serialization(self):
        m = self.module()
        self.assertEqual(m.expr(m.parse('ite (lit (boolean true)) (lit (int 1)) (lit (int 2))')),
                         'if (true) then (1) else (2)')
        self.assertEqual(m.expr(m.parse('recExprCons "x" (lit (int 1)) recExprNil')),
                         '{x: 1}')
        self.assertEqual(m.expr(m.parse('binaryApp contains (setExprCons (lit (int 1)) setExprNil) (lit (int 1))')),
                         '([1]).contains(1)')

    def test_nested_attribute_product_from_coq_show(self):
        m = self.module()
        self.assertEqual(m.attrs(m.parse('[(("age", false), intType)]')), 'age: Long')

    def test_same_expression_different_environment_is_different_payload(self):
        m = self.module()
        template = ('Original.mkInput [] [] [] '
                    '(MkEnvironment (MkSchema [] []) '
                    '(MkRequest (MkName "User" []) (MkEntityUID (MkName "Action" []) "%s") '
                    '(MkName "Doc" []) [])) [] intType (lit (int 7), somepaths [])')
        a, b = [m.payload(template % action) for action in ['read', 'write']]
        self.assertNotEqual(a, b)
        self.assertEqual(a.split('|||')[-1], b.split('|||')[-1])
        self.assertIn('Action::"read"', a)

    def test_protocol_delimiter_rejected_not_silently_changed(self):
        m = self.module()
        with self.assertRaises(ValueError):
            m.wire(['schema|||oops', 'p', 'a', 'r', 'true'])

    def test_no_result_verdict_is_accounted_for(self):
        m = self.module()
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)
            (p / 'attempts.jsonl').write_text(json.dumps({'id': 'a', 'input_coq': None}) + '\n')
            (p / 'verdicts.jsonl').write_text(json.dumps({'id': 'a', 'overall': 'no_generation'}) + '\n')
            rows, counts = m.read_batch(p)
            self.assertEqual(rows, [])
            self.assertEqual(counts, {'attempts': 1, 'no_result': 1})

    def test_branch_outcomes_not_line_or_region_counts(self):
        m = self.module()
        export = {'data': [{'files': [
            {'filename': '/r/cedar-policy-core-4.8.2/src/validator/typecheck.rs',
             'branches': [[1, 2, 1, 8, 5, 0, 0, 0, 4], [2, 1, 2, 9, 2, 3, 0, 0, 4]]},
            {'filename': '/r/serde/src/lib.rs', 'branches': [[1, 1, 1, 2, 9, 9, 0, 0, 4]]}
        ]}]}
        result = m.branch_sets(export)
        self.assertEqual(len(result['cedar']['covered']), 3)
        self.assertEqual(len(result['cedar']['total']), 4)
        self.assertEqual(result['typecheck'], result['validator'])

    def test_cedar_generated_parsers_are_in_coverage_denominator(self):
        m = self.module()
        export = {'data': [{'files': [
            {'filename': '/target/debug/build/cedar-policy-core/hash/out/src/parser/grammar.rs',
             'branches': [[1, 1, 1, 9, 1, 0, 0, 0, 4]]},
            {'filename': '/target/debug/build/cedar-policy-core/hash/out/src/validator/cedar_schema/grammar.rs',
             'branches': [[2, 1, 2, 9, 1, 1, 0, 0, 4]]}]}]}
        groups = m.branch_sets(export)
        self.assertEqual(len(groups['cedar']['total']), 4)
        self.assertEqual(len(groups['cedar']['covered']), 3)
        self.assertEqual(len(groups['validator']['total']), 2)

    def test_stalled_reader_has_a_write_deadline(self):
        m = self.module()
        read_fd, write_fd = os.pipe2(os.O_NONBLOCK)
        try:
            with self.assertRaises(TimeoutError):
                m.write_deadline(write_fd, b'x' * 1000000, .01)
        finally:
            os.close(read_fd); os.close(write_fd)

    def test_all_versions_uses_evaluation_inputs_and_keeps_run_identity(self):
        m = self.module()
        summary = {'baseline': {'label': 'eval'}, 'held_out_baseline': {'label': 'held'},
                   'runs': {run: {'last_candidate_id': 'v002',
                       'held_out': {'measurement': {'label': 'held-last'}},
                       'adopted': [{'id': v, 'measurement': {'label': run + v}}
                                   for v in ['v001', 'v002']]}
                            for run in ['run-001', 'run-002']}}
        groups, seeds = m.select_groups(summary, 'all-versions')
        self.assertEqual(seeds, [101, 202, 303, 404, 505])
        self.assertEqual([(r, v) for r, v, _ in groups],
                         [('P0', 'P0'), ('run-001', 'v001'), ('run-001', 'v002'),
                          ('run-002', 'v001'), ('run-002', 'v002')])
        self.assertEqual(groups[0][2]['label'], 'eval')
        final, held_seeds = m.select_groups(summary, 'final-heldout')
        self.assertEqual(held_seeds, [1101, 1202, 1303, 1404, 1505])
        self.assertEqual([v for _, v, _ in final], ['P0', 'v002', 'v002'])
        self.assertEqual(final[-1][2]['label'], 'held-last')

    def test_report_keeps_versions_separate_and_rejects_missing_cohorts(self):
        from scripts.cedar.report_rust_coverage import summarize
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            keys = ['P0-P0-101', 'run-001-v001-101', 'run-001-v002-101']
            manifest = {'mode': 'all-versions', 'seeds': [101],
                        'cohorts': {k: {} for k in keys}}
            (root / 'manifest.json').write_text(json.dumps(manifest))
            (root / 'completion.json').write_text('{"status":"completed"}')
            def export(count):
                return {'data': [{'files': [{'filename': '/r/cedar-policy-core-4.8.2/src/validator/typecheck.rs',
                    'branches': [[1, 1, 1, 9, count, 0, 0, 0, 4]]}]}]}
            (root / 'empty-control').mkdir()
            (root / 'empty-control/coverage.json').write_text(json.dumps(export(0)))
            results = {}
            for budget in ['outer-10000', 'equal-valid']:
                results[budget] = {}
                for i, key in enumerate(keys):
                    folder = root / budget / key
                    folder.mkdir(parents=True)
                    (folder / 'coverage.json').write_text(json.dumps(export(i % 2)))
                    results[budget][key] = {'inputs': 1, 'responses': {'true': 1}}
            (root / 'results.json').write_text(json.dumps(results))
            data = summarize(root)['budgets']['outer-10000']
            self.assertEqual(set(data), {'P0', 'run-001-v001', 'run-001-v002'})
            self.assertEqual(data['run-001-v001']['scopes']['cedar']['mean_covered'], 1)
            self.assertEqual(data['run-001-v002']['scopes']['cedar']['mean_covered'], 0)
            del results['equal-valid'][keys[-1]]
            (root / 'results.json').write_text(json.dumps(results))
            with self.assertRaises(AssertionError):
                summarize(root)


if __name__ == '__main__':
    unittest.main()
