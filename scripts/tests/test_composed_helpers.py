"""Ordered external helper composition uses real native requests and replay."""
import copy
import json
import unittest

from scripts.tests import test_property_exec as native
SPEC = native.SPEC

STATUS_CONFIG = {'schema_version': 1, 'observations': [
    {'id': 'run', 'relation': 'Run', 'observe': []}]}
SAME = '''relation Exists:
  |- nat
  hint(input %0)
rule Exists/value:
  |- n
  -- Run: n ~> _

relation Same:
  nat ~> nat
  hint(input %0 %1)
rule Same/accepted:
  n ~> m
  -- Exists: |- n
  -- Exists: |- m
rule Same/rejected:
  n ~> m
  -- Exists:/ |- n
  -- Exists:/ |- m

property same:
  (n : nat) (m : nat)
  Same: n ~> m
'''


NEGATED = SAME.replace('property same:', 'relation Different:\n  nat ~> nat\n  hint(input %0 %1)\nrule Different/value:\n  n ~> m\n  -- Same:/ n ~> m\n\nproperty same:').replace('  Same: n ~> m\n', '  Different: n ~> m\n')


class ComposedHelperTests(unittest.TestCase):
    setUp = native.NativePropertyExecutorTests.setUp
    load = native.NativePropertyExecutorTests.load
    invoke = native.NativePropertyExecutorTests.invoke
    # Reuse the native harness, without copying its tests into this suite.
    def composition(self, source=SAME, config=STATUS_CONFIG):
        plan = self.load(source, spec=SPEC + '\nvar m : nat\nvar x : nat\n', config=config)
        self.assertEqual(plan['unsupported'], [])
        self.assertEqual(self.invoke(plan, 'audit', {}, []), {'valid': True})
        return plan

    def execute(self, plan, statuses, inputs=None):
        inputs = {'n': 3, 'm': 4} if inputs is None else inputs
        trace, requests = [], []
        for index, call in enumerate(plan['calls']):
            projected = self.invoke(plan, 'request', inputs, trace, index)
            value = projected.get('input')
            status = statuses.get(value[0], 'success') if projected['ready'] else 'blocked'
            if projected['ready']:
                requests.append(value)
            trace.append({'occurrence_id': call['id'], 'relation_id': call['relation'],
                          'input': value, 'status': status, 'observation': {}})
            self.invoke(plan, 'validate', inputs, trace)
        return self.invoke(plan, 'check', inputs, trace), requests, trace

    def test_same_acceptance_truth_table_and_short_circuit(self):
        plan = self.composition()
        for left, right, verdict, requests in [
            ('success', 'success', 'pass', [[3], [4]]),
            ('success', 'relation_failure', 'fail', [[3], [4], [3]]),
            ('relation_failure', 'success', 'fail', [[3], [3], [4]]),
            ('relation_failure', 'relation_failure', 'pass', [[3], [3], [4]]),
        ]:
            with self.subTest(left=left, right=right):
                result, actual, _ = self.execute(plan, {3: left, 4: right})
                self.assertEqual(result['verdict'], verdict)
                self.assertEqual(actual, requests)

    def test_errors_stop_alternatives_and_are_not_negated(self):
        for negated in (False, True):
            plan = self.composition(NEGATED if negated else SAME)
            for error in ('abort', 'execution_error'):
                result, requests, _ = self.execute(plan, {3: error})
                self.assertEqual(result['verdict'], 'error')
                self.assertEqual(requests, [[3]])

    def test_negated_composition_inverts_aggregate_result(self):
        plan = self.composition(NEGATED)
        for statuses, verdict in [({3: 'success', 4: 'success'}, 'fail'),
                                  ({3: 'success', 4: 'relation_failure'}, 'pass')]:
            result, _, _ = self.execute(plan, statuses)
            self.assertEqual(result['verdict'], verdict)

    def test_skipped_trace_call_cannot_be_forged_or_activated(self):
        plan = self.composition()
        _, _, trace = self.execute(plan, {})
        forged = copy.deepcopy(trace)
        forged[2].update(status='success', input=[3])
        with self.assertRaisesRegex(ValueError, 'blocked|unavailable'):
            self.invoke(plan, 'validate', {'n': 3, 'm': 4}, forged)

    def test_composition_cannot_read_hidden_primitive_outputs(self):
        source = SAME.replace('-- Exists: |- n\n  -- Exists: |- m',
                              '-- Run: n ~> x\n  -- Exists: |- x', 1)
        plan = self.load(source, spec=SPEC + '\nvar m : nat\nvar x : nat\n', config=STATUS_CONFIG)
        self.assertTrue(plan['unsupported'])

    def test_distinct_primitives_and_swapped_helper_inputs(self):
        source = SAME[:SAME.index('relation Same:')] + '''relation Both:
  nat ~> nat
  hint(input %0 %1)
rule Both/value:
  n ~> m
  -- Exists: |- m
  -- Parse: n ~> _

property both:
  (n : nat) (m : nat)
  Both: m ~> n
'''
        config = {'schema_version': 1, 'observations': [*STATUS_CONFIG['observations'],
            {'id': 'parse', 'relation': 'Parse', 'observe': []}]}
        plan = self.composition(source, config)
        result, requests, trace = self.execute(plan, {})
        self.assertEqual(result['verdict'], 'pass')
        self.assertEqual(requests, [[3], [4]])
        self.assertEqual([entry['relation_id'] for entry in trace], ['Run', 'Parse'])
        result, requests, _ = self.execute(plan, {3: 'relation_failure'})
        self.assertEqual(result['verdict'], 'fail')
        self.assertEqual(requests, [[3]])

    def test_helper_input_guard_and_call_free_alternative(self):
        source = SAME.replace('  -- Exists: |- n\n  -- Exists: |- m',
                              '  -- if $(n < m)', 1)
        plan = self.composition(source)
        result, requests, _ = self.execute(plan, {3: 'abort', 4: 'abort'})
        self.assertEqual(result['verdict'], 'pass')
        self.assertEqual(requests, [])
        result, requests, _ = self.execute(plan, {4: 'relation_failure', 3: 'relation_failure'},
                                            {'n': 4, 'm': 3})
        self.assertEqual(result['verdict'], 'pass')
        self.assertEqual(requests, [[4], [3]])

    def test_composition_condition_and_negated_condition(self):
        for negative, verdict in [(False, 'pass'), (True, 'fail')]:
            source = SAME.replace('  Same: n ~> m\n',
                '  true\n  -- Same' + (':/' if negative else ':') + ' n ~> m\n')
            plan = self.composition(source)
            result, requests, _ = self.execute(plan, {})
            self.assertEqual(result['verdict'], verdict)
            self.assertEqual(requests, [[3], [4]])

    def test_composition_accepts_observed_inputs(self):
        source = SAME.replace('  Same: n ~> m\n',
            '  Same: x ~> m\n  -- Parse: n ~> x\n')
        config = {'schema_version': 1, 'observations': [*STATUS_CONFIG['observations'],
            {'id': 'parse', 'relation': 'Parse', 'observe': ['%1']}]}
        plan = self.composition(source, config)
        first = {'occurrence_id': 'condition.0', 'relation_id': 'Parse', 'input': [3],
                 'status': 'success', 'observation': {'%1': 9}}
        self.assertEqual(self.invoke(plan, 'request', {'n': 3, 'm': 4}, [first], 1),
                         {'ready': True, 'input': [9]})

    def test_native_audit_reconstructs_composition_membership(self):
        original = self.composition()
        for change in ('remove', 'reorder', 'relation', 'index', 'negation', 'dependency'):
            plan = copy.deepcopy(original)
            if change == 'remove':
                plan['calls'].pop()
            elif change == 'reorder':
                plan['calls'].reverse()
            elif change == 'relation':
                plan['calls'][0]['relation'] = 'Parse'
            elif change == 'index':
                plan['calls'][0]['leaf_index'] = 1
            elif change == 'negation':
                plan['calls'][0]['invert'] = True
            else:
                plan['calls'][0]['dependencies'] = ['fake']
            (self.folder / 'plan.json').write_text(json.dumps(plan))
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'composition'):
                self.invoke(plan, 'audit', {}, [])

    def test_recursive_and_output_constrained_helpers_remain_unsupported(self):
        for source in [SAME.replace('-- Exists: |- m', '-- Same: n ~> m', 1),
                       SAME.replace('-- Run: n ~> _', '-- Run: n ~> n')]:
            plan = self.load(source, spec=SPEC + '\nvar m : nat\n', config=STATUS_CONFIG)
            self.assertTrue(plan['unsupported'])

    def test_dynamic_functions_hidden_inside_composition_are_audited(self):
        source = SAME.replace('-- Exists: |- m', '-- Exists: |- $opaque(m)', 1)
        plan = self.load(source, spec=SPEC + '\nvar m : nat\nextern dec $opaque(nat) : nat\n',
                         config=STATUS_CONFIG)
        self.assertEqual(plan['unsupported'], [])
        with self.assertRaisesRegex(ValueError, 'dynamic function call'):
            self.invoke(plan, 'audit', {}, [])

    def test_partial_input_expressions_keep_native_al_failure_guards(self):
        source = """relation Checked:
  nat* ~> nat
  hint(input %0 %1)
rule Checked/value:
  xs ~> m
  -- if $(xs[0] = m)
  -- Run: m ~> _

relation Rejected:
  nat* ~> nat
  hint(input %0 %1)
rule Rejected/value:
  xs ~> m
  -- Checked:/ xs ~> m

property guarded:
  (xs : nat*) (m : nat)
  Rejected: xs ~> m
"""
        variants = [source,
            source.replace('  -- if $(xs[0] = m)\n  -- Run: m ~> _', '  -- Run: xs[0] ~> _'),
            source.replace('  -- if $(xs[0] = m)\n  -- Run: m ~> _', '  -- Exists: |- xs[0]')]
        exists = SAME[:SAME.index('relation Same:')]
        for variant in variants:
            with self.subTest(source=variant):
                plan = self.load(exists + variant, spec=SPEC + '\nvar m : nat\nvar xs : nat*\n',
                                 config=STATUS_CONFIG)
                self.assertEqual(plan['unsupported'], [])
                self.assertEqual(self.invoke(plan, 'audit', {}, []), {'valid': True})
                result, requests, _ = self.execute(plan, {}, {'xs': [], 'm': 3})
                self.assertEqual(result['verdict'], 'pass')
                self.assertEqual(requests, [])

    def test_partial_composed_invocation_skips_calls_as_normal_failure(self):
        source = SAME.replace('(n : nat) (m : nat)', '(xs : nat*) (m : nat)').replace(
            '  Same: n ~> m\n', '  Same: xs[0] ~> m\n')
        plan = self.load(source, spec=SPEC + '\nvar m : nat\nvar xs : nat*\n', config=STATUS_CONFIG)
        self.assertEqual(plan['unsupported'], [])
        result, requests, _ = self.execute(plan, {}, {'xs': [], 'm': 3})
        self.assertEqual(result['verdict'], 'fail')
        self.assertEqual(requests, [])


class ComposedCertificationTests(unittest.TestCase):
    def test_certified_generator_run_and_saved_trace_replay(self):
        import tempfile
        from pathlib import Path
        from scripts.tests import ROOT, ORDERED, SCRATCH
        from scripts.property.workflow import emit_property, check_property
        from scripts.property.runner import run_property, recheck_trace, rerun_case

        with tempfile.TemporaryDirectory(prefix='Composed', dir=SCRATCH) as tmp:
            folder = Path(tmp)
            base = '.'.join(folder.relative_to(ROOT).parts)
            source = folder / 'property.watsup'
            source.write_text(SAME.replace('Run:', 'Copy:'))
            spec = folder / 'spec.watsup'
            spec.write_text((ORDERED / 'spec.watsup').read_text() + '\nvar m : nat\n')
            external = folder / 'external.toml'
            external.write_text('schema_version = 1\n[[external]]\nid = "copy"\nobserve = []\n')
            output = emit_property(spec_paths=[spec], property_path=source,
                config_path=ORDERED / 'observations.toml', external_path=external, name='same',
                proof_module=base + '.Proof', property_proof='Composed.property_correct',
                generator_module=base + '.Generator', generator='ComposedGenerator.generator')
            for filename, template in [('Proof.lean', 'composed_proof.lean.in'),
                                       ('Generator.lean', 'composed_generator.lean.in')]:
                (folder / filename).write_text((ORDERED / 'templates' / template).read_text()
                    .replace('@CONTRACT@', base + '.bundle.Contract').replace('@PROOF@', base + '.Proof'))
            bundle = check_property(output)
            for mode, expected_calls in [('correct', 2), ('reject', 3)]:
                result = run_property(bundle, implementation=ORDERED / 'implementations' / (mode + '.toml'),
                                      output=folder / mode, count=1, size=5, seed=7)
                self.assertEqual(result.status, 'passed')
                case = folder / mode / 'case-000000'
                trace = case / 'trace.json'
                self.assertEqual(recheck_trace(bundle, trace).verdict, 'pass')
                entries = json.loads(trace.read_text())['entries']
                self.assertEqual(sum(entry['status'] != 'blocked' for entry in entries), expected_calls)
            fresh = rerun_case(bundle, folder / 'correct' / 'case-000000', folder / 'rerun',
                               implementation=ORDERED / 'implementations/reject.toml')
            self.assertEqual(fresh.verdict, 'pass')
