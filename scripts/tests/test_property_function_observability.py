"""Function bodies preserve external observation and projection obligations."""
from contextlib import contextmanager
from pathlib import Path
import sys
import tempfile
import unittest

from scripts.property.compiler import CompileError, compile_debug, compile_replay, compile_spec
from scripts.property.replay import replay


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'scripts/tests/fixtures/property/observability/function_external.watsup'
INPUT = {'x': {'type': 'nat', 'value': '7'}}


class FunctionObservabilityTests(unittest.TestCase):
    @contextmanager
    def model(self, positions, *, dead=False, missing=False, goal_only=False,
              replacements=()):
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems') as temp:
            directory = Path(temp)
            contents = SOURCE.read_text()
            if dead:
                contents = contents.replace('def $inner(x) = y', 'def $inner(x) = x')
            if missing:
                contents = contents.replace('relation E: nat nat hint(input %0)\n'
                    'rule E/spec: x y\n  -- if y = x',
                    'extern relation E: nat nat hint(input %0)')
            if goal_only:
                contents = contents.replace('-- if z = $outer(x)', '-- if z = x')
                contents = contents.replace('rule Goal/main: x z\n  -- if z = x',
                    'rule Goal/main: x z\n  -- if z = $outer(x)')
            for before, after in replacements:
                self.assertIn(before, contents)
                contents = contents.replace(before, after)
            source = directory / SOURCE.name
            source.write_text(contents)
            config = directory / 'Property.toml'
            config.write_text('precondition = "Pre"\ngoal = "Goal"\n'
                '[[external]]\nrelation = "E"\nadapter = "external"\n'
                f'conversion = "json-v1"\nobserved_outputs = {positions}\n')
            yield compile_spec(source, config), directory

    def execute(self, model, directory, positions):
        script = directory / 'external.py'
        outputs = [{'position': position, 'value': {'type': 'nat', 'value': '7'}}
                   for position in positions]
        script.write_text('import json,sys\nrequest=json.loads(sys.stdin.readline())\n'
            'print(json.dumps({"status":"returned","fresh_id":request["fresh_id"]+1,'
            '"outputs":' + repr(outputs) + '}),flush=True)\n')
        return replay(compile_replay(model), INPUT,
                      {'external': [sys.executable, str(script)]})

    def test_nested_function_return_requires_observed_external_output(self):
        with self.model([]) as (model, _):
            with self.assertRaises(CompileError) as caught:
                compile_replay(model)
            self.assertIn('inner', str(caught.exception))
            self.assertIn('E output slot 0', str(caught.exception))
            self.assertEqual(caught.exception.details['helper_path'],
                             ['Pre', '$outer', '$inner'])
            self.assertEqual(caught.exception.details['premise']['kind'], 'return:0')
            self.assertEqual(caught.exception.details['guaranteed_outputs']['$inner'], [])

    def test_helper_callback_cannot_hide_external_observation_requirements(self):
        with self.model([], replacements=[
            ('dec $outer(nat) : nat',
             'dec $apply<X>(def $f(X) : X, X) : X\n'
             'def $apply<X>(def $f, X) = $f(X)\n'
             'dec $outer(nat) : nat'),
            ('def $outer(x) = $inner(x)', 'def $outer(x) = $apply<nat>(def $inner, x)'),
        ]) as (model, _):
            with self.assertRaisesRegex(CompileError, 'higher.order.*observation'):
                compile_replay(model)

    def test_full_observation_reaches_function_calls_and_executes(self):
        with self.model([0]) as (model, directory):
            program = compile_replay(model)
            self.assertTrue(program.analysis['external_classification']['Pre'])
            self.assertEqual(program.analysis['classification_reasons']['Pre']['boundaries'], ['E'])
            result = self.execute(model, directory, [0])
            self.assertEqual(result.status, 'passed', result)
            self.assertEqual(result.external_call_count, 1)
            self.assertEqual(result.trace['fresh_id'], 1)

    def test_dead_function_local_output_is_projected_but_call_and_fresh_remain(self):
        with self.model([], dead=True) as (model, directory):
            result = self.execute(model, directory, [])
            self.assertEqual(result.status, 'passed', result)
            self.assertEqual(result.external_call_count, 1)
            self.assertEqual(result.trace['fresh_id'], 1)
            self.assertFalse(any(binding['label'] == '$inner.y'
                                 for binding in result.trace['bindings']))

    def test_function_return_call_in_relation_conclusion_is_analyzed(self):
        replacement = [('rule Pre/main: x z\n  -- if z = $outer(x)',
                        'rule Pre/main: x $outer(x)')]
        with self.model([], replacements=replacement) as (model, _):
            with self.assertRaisesRegex(CompileError, 'E output slot 0'):
                compile_replay(model)
        with self.model([0], replacements=replacement) as (model, directory):
            self.assertEqual(self.execute(model, directory, [0]).status, 'passed')

    def test_function_condition_cannot_use_dead_unobserved_output(self):
        with self.model([], dead=True, replacements=[
                ('  -- E: x y', '  -- E: x y\n  -- if y = 7')]) as (model, _):
            with self.assertRaisesRegex(CompileError, 'E output slot 0'):
                compile_replay(model)

    def test_function_fallback_preserves_failed_clause_call_and_fresh(self):
        with self.model([], dead=True, replacements=[
                ('def $inner(x) = x\n  -- E: x y',
                 'def $inner(x) = x\n  -- E: x y\n  -- if x = 0\n'
                 'def $inner(x) = x\n  -- otherwise')]) as (model, directory):
            result = self.execute(model, directory, [])
            self.assertEqual(result.status, 'passed', result)
            self.assertEqual(result.external_call_count, 1)
            self.assertEqual(result.trace['fresh_id'], 1)

    def test_pre_function_requires_transitive_specification_definition(self):
        with self.assertRaisesRegex(CompileError, 'specification definitions for E'):
            with self.model([0], missing=True):
                pass

    def test_goal_function_missing_definition_only_blocks_debug(self):
        with self.model([0], missing=True, goal_only=True) as (model, directory):
            program = compile_debug(model)
            self.assertFalse(program.available)
            self.assertIn('E', program.missing)
            result = self.execute(model, directory, [0])
            self.assertEqual(result.status, 'passed', result)
            self.assertEqual(result.external_call_count, 1)


if __name__ == '__main__':
    unittest.main()
