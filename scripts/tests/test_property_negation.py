"""Native negation works in declarations, composed helpers, and adapter replay."""
from dataclasses import asdict
from argparse import Namespace
import json
from pathlib import Path
import sys
import tempfile
import unittest

from scripts.property.bridge import ROOT, STATE
from scripts.property.compiler import compile_debug, compile_replay, compile_spec
from scripts.property.debug import debug
from scripts.property.declaration import lower_property
from scripts.property.model import CompileError
from scripts.property.replay import replay


SPEC = ROOT / 'scripts/tests/fixtures/property/bridge/negation.watsup'


class NegationTests(unittest.TestCase):
    def setUp(self):
        self.work = Path(tempfile.mkdtemp(prefix='property-negation.', dir=STATE / 'checks'))

    def lower(self, goal, conditions='', inputs='(x : nat)'):
        path = self.work / 'Property.spectec'
        path.write_text(f'property [negation]:\n  {inputs}\n  {goal}\n' + conditions)
        lowered = lower_property(path, [SPEC], self.work / 'lowered')
        return lowered

    def model(self, goal, conditions='', inputs='(x : nat)', external=None, observed=()):
        lowered = self.lower(goal, conditions, inputs)
        if external:
            with lowered.config.open('a') as config:
                config.write(f'\n[[external]]\nrelation = "{external}"\n'
                             'adapter = "test"\nconversion = "json-v1"\n'
                             f'observed_outputs = {list(observed)}\n')
        return compile_spec(lowered.source, lowered.config)

    def payload(self, model, values):
        return {item['name']: {'type': 'nat', 'value': str(value)}
                for item, value in zip(model.inputs, values)}

    def replay(self, model, values=(1,), accepted=(), *, observed=None, bad=None, timeout=5):
        adapter = self.work / 'adapter.py'
        adapter.write_text('import json,sys,time\nfor line in sys.stdin:\n'
                           ' request=json.loads(line)\n' +
                           (' time.sleep(2)\n' if bad == 'timeout' else '') +
                           f' accepted={list(accepted)!r}\n'
                           ' value=int(request["input"][0]["value"])\n'
                           ' response={"status":"returned" if value in accepted else "no_match",'
                           '"fresh_id":request["fresh_id"]}\n'
                           ' if response["status"]=="returned":\n'
                           '  response["outputs"]=' +
                           ('[]' if observed is None else
                            repr([{'position': 0, 'value': {'type': 'nat', 'value': str(observed)}}])) + '\n' +
                           (' response={"status":"error"}\n' if bad == 'protocol' else '') +
                           ' print(json.dumps(response),flush=True)\n')
        result = replay(compile_replay(model), self.payload(model, values),
                        {'test': [sys.executable, str(adapter)]}, timeout=timeout)
        (self.work / 'result.json').write_text(json.dumps(asdict(result), indent=2))
        return result

    def test_direct_goal_and_condition_use_native_negation(self):
        goal = self.model('Zero:/ |- x')
        self.assertEqual(debug(compile_debug(goal), self.payload(goal, (1,))).status, 'passed')
        self.assertEqual(debug(compile_debug(goal), self.payload(goal, (0,))).status, 'failed')
        condition = self.model('true', '  -- Zero:/ |- x\n')
        self.assertEqual(debug(compile_debug(condition), self.payload(condition, (1,))).status, 'passed')
        self.assertEqual(debug(compile_debug(condition), self.payload(condition, (0,))).status,
                         'precondition_failed')

    def test_native_rejects_output_bearing_or_unbound_negation(self):
        for goal, conditions, pattern in [
            ('Run:/ x ~> x', '', 'output'),
            ('true', '  -- Zero:/ |- missing\n', 'bound'),
            ('Zero:/ x x', '', 'notation|match|expected'),
        ]:
            with self.subTest(goal=goal, conditions=conditions):
                with self.assertRaisesRegex(CompileError, pattern):
                    self.lower(goal, conditions)

    def test_composed_external_helpers_and_their_negation_have_same_truth_table(self):
        for negative in (False, True):
            model = self.model('Same:' + ('/' if negative else '') + ' x ~> y',
                               inputs='(x : nat) (y : nat)', external='Run', observed=(0,))
            for accepted in ((), (1,), (2,), (1, 2)):
                with self.subTest(negative=negative, accepted=accepted):
                    result = self.replay(model, (1, 2), accepted, observed=7)
                    holds = (1 in accepted) == (2 in accepted)
                    self.assertEqual(result.status, 'passed' if holds != negative else 'failed', result)
                    self.assertEqual(result.external_call_count, 2 if accepted == (1, 2) else 3)

    def test_negative_external_preserves_no_match_errors_and_timeout(self):
        model = self.model('Zero:/ |- x', external='Zero')
        self.assertEqual(self.replay(model).status, 'passed')
        self.assertEqual(self.replay(model, accepted=(1,)).status, 'failed')
        self.assertEqual(self.replay(model, bad='protocol').status, 'execution_error')
        self.assertEqual(self.replay(model, bad='timeout', timeout=0.2).status, 'unknown')

    def test_negative_helper_can_ignore_hidden_outputs_but_cannot_read_them(self):
        model = self.model('Exists:/ |- x', external='Run')
        self.assertEqual(self.replay(model).status, 'passed')
        self.assertEqual(self.replay(model, accepted=(1,)).status, 'failed')
        model = self.model('Guard:/ |- x', external='Run')
        with self.assertRaisesRegex(CompileError, 'Run output slot 0'):
            compile_replay(model)

    def test_negative_preconditions_retain_external_status_and_control(self):
        cases = [
            ('  -- Zero:/ |- x\n', 'Zero', (), (1,), None),
            ('  -- Status:/ |- x\n', 'Zero', (), (1,), None),
            ('  -- Zero:/ |- x\n  -- if x = 8\n', 'Zero', (), (), None),
            ('  -- Exists:/ |- x\n  -- if x = 8\n', 'Run', (0,), (), 7),
            ('  -- Guard:/ |- x\n  -- if x = 8\n', 'Run', (0,), (1,), 7),
            ('  -- Alternatives:/ |- x\n  -- if x = 8\n', 'Run', (0,), (1,), 7),
        ]
        for conditions, external, observed, accepted, value in cases:
            with self.subTest(conditions=conditions):
                model = self.model('true', conditions, external=external, observed=observed)
                result = self.replay(model, accepted=accepted, observed=value)
                self.assertEqual(result.status, 'implementation_bug', result)
                self.assertEqual(len(result.trace['failure']['external_events']), 1)

    def test_failed_negative_helper_ignoring_external_argument_is_independent(self):
        model = self.model('true', '  -- Run: x ~> y\n  -- Ignore:/ |- y\n',
                           external='Run', observed=(0,))
        result = self.replay(model, accepted=(1,), observed=7)
        self.assertEqual(result.status, 'execution_error', result)
        self.assertEqual(result.external_call_count, 1)
        self.assertEqual(result.trace['failure']['external_events'], [])

    def test_negation_of_recovered_fallback_does_not_blame_discarded_branch(self):
        model = self.model('true', '  -- Recovered:/ |- x\n', external='Run', observed=(0,))
        result = self.replay(model, accepted=(1,), observed=7)
        self.assertEqual(result.status, 'execution_error', result)
        self.assertEqual(result.external_call_count, 1)
        self.assertEqual(result.trace['failure']['external_events'], [])

    def test_nested_negation_does_not_revive_discarded_branch_dependencies(self):
        model = self.model('true', '  -- RejectedRecovered:/ |- x\n  -- if x = 8\n',
                           external='Run', observed=(0,))
        result = self.replay(model, accepted=(1,), observed=7)
        self.assertEqual(result.status, 'execution_error', result)
        self.assertEqual(result.external_call_count, 1)
        self.assertEqual(result.trace['failure']['external_events'], [])

    def test_successful_negative_helper_ignoring_external_argument_is_independent(self):
        model = self.model('true', '  -- Run: x ~> y\n  -- Never:/ |- y\n  -- if x = 8\n',
                           external='Run', observed=(0,))
        result = self.replay(model, accepted=(1,), observed=7)
        self.assertEqual(result.status, 'execution_error', result)
        self.assertEqual(result.external_call_count, 1)
        self.assertEqual(result.trace['failure']['external_events'], [])

    def test_native_argument_errors_are_not_inverted_with_the_judgment(self):
        model = self.model('Zero:/ |- $(x / 0)', external='Zero')
        result = self.replay(model)
        self.assertEqual(result.status, 'execution_error', result)
        self.assertEqual(result.external_call_count, 0)

    def test_recursive_failure_unwinds_before_independent_parent_fallback(self):
        model = self.model('true', '  -- Run: x ~> y\n  -- Recur:/ x ~> y\n',
                           external='Run', observed=(0,))
        result = self.replay(model, accepted=(1,), observed=7)
        self.assertEqual(result.status, 'execution_error', result)
        self.assertEqual(result.external_call_count, 1)
        self.assertEqual(result.trace['failure']['external_events'], [])


class NegationWorkflowTests(unittest.TestCase):
    def test_declaration_prepare_equivalence_sample_debug_and_composed_replay(self):
        from scripts import check
        from scripts.property.commands import execute

        work = Path(tempfile.mkdtemp(prefix='negation-workflow.', dir=STATE / 'checks'))
        source = work / 'Spec.watsup'
        source.write_bytes(SPEC.read_bytes())
        manifest = work / 'Specification.toml'
        manifest.write_text('id="negation"\nsources=["Spec.watsup"]\nprofile="fixture"\n')
        prop = work / 'property'
        prop.mkdir()
        (prop / 'Property.spectec').write_text('property [different_acceptance]:\n'
            '  (x : nat)\n  Same:/ x ~> 0\n  -- Zero:/ |- x\n')
        adapter = work / 'Adapter.toml'
        adapter.write_text('specification="negation"\n[[external]]\nrelation="Run"\n'
            'adapter="run"\ncommand=["python3","adapter.py"]\n'
            'conversion="json-v1"\nobserved_outputs=[]\n')
        (work / 'adapter.py').write_text('import json,sys\nfor line in sys.stdin:\n'
            ' r=json.loads(line)\n'
            ' response={"status":"returned" if int(r["input"][0]["value"]) else "no_match",'
            '"fresh_id":r["fresh_id"]}\n'
            ' if response["status"]=="returned": response["outputs"]=[]\n'
            ' print(json.dumps(response),flush=True)\n')
        args = Namespace(property=prop, action='sample', spec=manifest, implementation=None,
                         target='spec', timeout=20, candidate='v001', count=6, size=16, seed=0,
                         input_json=None, samples_file=None)
        path, ok = execute(args)
        report = json.loads(path.read_text())
        self.assertTrue(ok, report)
        self.assertGreater(report['generated'], 0)
        args.samples_file = Path(report['samples_file'])
        samples = json.loads(args.samples_file.read_text())
        self.assertTrue(all(s is None or int(s['x']['value']) != 0 for s in samples))
        original = (prop / 'Original.v').read_bytes()
        session = check.Session(prop)
        session.check()
        session.finish()
        self.assertEqual(session.report['assumptions'], [])
        for action, status, calls in [('debug', 'failed', 0), ('replay', 'passed', 3)]:
            args.action, args.implementation = action, adapter
            path, ok = execute(args)
            result = json.loads(path.read_text())
            self.assertTrue(ok, result)
            self.assertEqual(result['status_counts'].get(status, 0), report['generated'], result)
            self.assertEqual(result['external_calls'], calls * report['generated'])
        self.assertEqual(source.read_bytes(), SPEC.read_bytes())
        self.assertEqual((prop / 'Original.v').read_bytes(), original)


if __name__ == '__main__':
    unittest.main()
