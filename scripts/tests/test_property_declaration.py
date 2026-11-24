"""Exercise property lowering through the real pinned SpecTec frontend."""
from pathlib import Path
from dataclasses import replace
import importlib
import json
import tempfile
import tomllib
import unittest

from scripts.property.bridge import STATE
from scripts.property.compiler import compile_spec, compile_replay
from scripts.property.engine import run_bridge
from scripts.property.model import CompileError

ROOT = Path(__file__).resolve().parents[2]
SPEC = ROOT / 'scripts/tests/fixtures/property/declaration/spec.watsup'


class DeclarationTests(unittest.TestCase):
    def setUp(self):
        try:
            self.api = importlib.import_module('scripts.property.declaration')
        except ModuleNotFoundError:
            self.fail('the declaration frontend is not implemented')
        directory = STATE / 'checks'
        directory.mkdir(parents=True, exist_ok=True)
        self.work = Path(tempfile.mkdtemp(prefix='declaration.', dir=directory))

    def lower(self, text, sources=None):
        path = self.work / 'Property.watsup'
        path.write_text(text)
        return self.api.lower_property(path, [SPEC] if sources is None else sources,
                                       self.work / 'lowered')

    def test_typed_inputs_witnesses_goal_and_original_trace_locations(self):
        lowered = self.lower('property [demo]:\n  (x : nat) (y : nat)\n'
                             '  c = $(x + 4)\n  -- External: x b\n  -- B: b c\n')
        self.assertEqual(lowered.name, 'demo')
        settings = tomllib.loads(lowered.config.read_text())
        self.assertEqual(set(settings), {'precondition', 'goal'})
        model = compile_spec(lowered.source, lowered.config)
        self.assertEqual([item['type'] for item in model.inputs], ['nat', 'nat'])
        self.assertEqual(list(model.pre_outputs), ['nat'])
        result = run_bridge('debug', lowered.source,
                            {'pre': model.precondition, 'goal': model.goal,
                             'input': [{'type': 'nat', 'value': 5},
                                       {'type': 'nat', 'value': 9}]})
        self.assertEqual(result['status'], 'passed')
        result = self.api.remap_locations(result, lowered.source_map)
        locations = [m['source'] for m in result['markers']]
        self.assertTrue(any('Property.watsup:4.' in loc for loc in locations), locations)
        self.assertTrue(any(str(SPEC) in loc for loc in locations), locations)
        json.dumps(lowered.source_map)

    def test_empty_inputs_and_no_witnesses(self):
        lowered = self.lower('property [constant]:\n  ()\n  true\n')
        model = compile_spec(lowered.source, lowered.config)
        self.assertEqual(model.inputs, ())
        result = run_bridge('debug', lowered.source,
                            {'pre': model.precondition, 'goal': model.goal, 'input': []})
        self.assertEqual(result['status'], 'passed')

    def test_relation_goal(self):
        lowered = self.lower('property [relation]:\n  (x : nat)\n  B: b c\n'
                             '  -- External: x b\n  -- B: b c\n')
        model = compile_spec(lowered.source, lowered.config)
        result = run_bridge('debug', lowered.source,
                            {'pre': model.precondition, 'goal': model.goal,
                             'input': [{'type': 'nat', 'value': 5}]})
        self.assertEqual(result['status'], 'passed')

    def test_computed_premise_and_false_goal_preserve_generation_condition(self):
        lowered = self.lower('property [false_goal]:\n  (x : nat)\n  false\n'
                             '  -- b = $(x + 4)\n')
        model = compile_spec(lowered.source, lowered.config)
        result = run_bridge('debug', lowered.source,
                            {'pre': model.precondition, 'goal': model.goal,
                             'input': [{'type': 'nat', 'value': 5}]})
        self.assertEqual(result['status'], 'failed')
        self.assertEqual(result['pre_outputs'], [])
        self.assertTrue(any(item['value'] == {'type': 'nat', 'value': '9'}
                            for item in result['bindings']))

    def test_nested_block_comments_in_original_sources_are_lexically_opaque(self):
        source = self.work / 'comments.watsup'
        source.write_text('(; (x : fake)\n (; property [bad]: ;)\n;)\n')
        lowered = self.lower('property [comments]:\n  (x : nat)\n'
                             '  (; -- Broken: missing ;) x = x\n', [source])
        model = compile_spec(lowered.source, lowered.config)
        self.assertEqual(len(model.inputs), 1)

    def test_remapping_preserves_runtime_text_values(self):
        lowered = self.lower('property [locations]:\n  (x : nat)\n  x = x\n')
        internal = next(iter(lowered.source_map['variables']))
        value = {'label': f'Pre.argument.{internal}',
                 'literal': {'type': 'text', 'value': internal}}
        mapped = self.api.remap_locations(value, lowered.source_map)
        self.assertEqual(mapped['label'], 'Pre.argument.x')
        self.assertEqual(mapped['literal']['value'], internal)

    def test_local_names_with_same_native_suffix_stem_have_independent_types(self):
        lowered = self.lower('property [names]:\n  (x_nat : nat) (x_text : text)\n'
                             '  x_text = "x_nat"\n  -- b_value = $(x_nat + 1)\n')
        model = compile_spec(lowered.source, lowered.config)
        self.assertEqual([item['type'] for item in model.inputs], ['nat', 'text'])
        result = run_bridge('debug', lowered.source,
                            {'pre': model.precondition, 'goal': model.goal,
                             'input': [{'type': 'nat', 'value': 5},
                                       {'type': 'text', 'value': 'x_nat'}]})
        self.assertEqual(result['status'], 'passed')
        self.assertEqual(result['pre_outputs'], [])

    def test_goal_diagnostics_preserve_original_columns_and_nested_source_positions(self):
        text = 'property [columns]:\n  (x : nat)\n  missing = x\n'
        with self.assertRaises(CompileError) as caught:
            self.lower(text)
        self.assertRegex(str(caught.exception), r'Property\.watsup:3\.3-3\.10')
        lowered = self.lower('property [columns]:\n  (x : nat)\n  x = x\n')
        row = next(row for row in lowered.source_map['lines']
                   if row['generated_file'] == str(lowered.source)
                   and row['line'] == 3 and '-- if' in lowered.source.read_text().splitlines()[row['generated_line'] - 1])
        internal = next(iter(lowered.source_map['variables']))
        line = lowered.source.read_text().splitlines()[row['generated_line'] - 1]
        location = {'left': {'file': str(lowered.source), 'line': row['generated_line'],
                             'column': line.index(internal)}}
        mapped = self.api.remap_locations(location, lowered.source_map)
        self.assertEqual(mapped, {'left': {'file': str(self.work / 'Property.watsup'),
                                           'line': 3, 'column': 2}})

    def test_unicode_before_variables_preserves_native_roles_and_source_columns(self):
        for goal in ['"é한🙂" = x', '(; é한🙂 ;) x = x']:
            with self.subTest(goal=goal):
                source = 'property [unicode]:\n  (x : text)\n  ' + goal + '\n'
                lowered = self.lower(source)
                model = compile_spec(lowered.source, lowered.config)
                result = run_bridge('debug', lowered.source,
                                    {'pre': model.precondition, 'goal': model.goal,
                                     'input': [{'type': 'text', 'value': 'é한🙂'}]})
                self.assertEqual(result['status'], 'passed')
                internal = next(name for name, public in lowered.source_map['variables'].items()
                                if public == 'x')
                lines = lowered.source.read_text().splitlines()
                row = next(row for row in lowered.source_map['lines']
                           if row['generated_file'] == str(lowered.source)
                           and row['line'] == 3 and '-- if' in lines[row['generated_line'] - 1])
                generated = lines[row['generated_line'] - 1]
                byte_column = len(generated[:generated.index(internal)].encode('utf-8'))
                location = {'file': str(lowered.source), 'line': row['generated_line'],
                            'column': byte_column}
                expected_column = source.splitlines()[2].index('x')
                mapped = self.api.remap_locations(location, lowered.source_map)
                self.assertEqual(mapped, {'file': str(self.work / 'Property.watsup'),
                                          'line': 3, 'column': expected_column})
                native = f"{lowered.source}:{row['generated_line']}.{byte_column + 1}"
                self.assertEqual(self.api.remap_locations(native, lowered.source_map),
                                 f'{self.work / "Property.watsup"}:3.{expected_column + 1}')
        lowered = self.lower('property [unicode_condition]:\n  (x : nat)\n  b = x\n'
                             '  -- (; é한🙂 ;) x = b\n')
        model = compile_spec(lowered.source, lowered.config)
        result = run_bridge('debug', lowered.source,
                            {'pre': model.precondition, 'goal': model.goal,
                             'input': [{'type': 'nat', 'value': 5}]})
        self.assertEqual(result['status'], 'passed')

    def test_unicode_diagnostics_use_original_character_columns(self):
        for goal in ['"é한🙂" = missing', '(; é한🙂 ;) missing = x']:
            with self.subTest(goal=goal):
                source = 'property [unicode_error]:\n  (x : text)\n  ' + goal + '\n'
                column = source.splitlines()[2].index('missing') + 1
                with self.assertRaises(CompileError) as caught:
                    self.lower(source)
                self.assertIn(f'Property.watsup:3.{column}-3.{column + 7}',
                              str(caught.exception))

    def test_goal_projects_witnesses_so_unused_external_output_needs_no_observation(self):
        spec = self.work / 'partial.watsup'
        spec.write_text('var n : nat\nvar m : nat\nvar u : nat\n'
                        'relation External: nat nat nat hint(input %0)\n'
                        'rule External/main: n m u\n  -- if m = $(n + 1)\n  -- if u = 99\n'
                        'relation B: nat nat hint(input %0)\n'
                        'rule B/main: n m\n  -- if m = $(n + 3)\n')
        lowered = self.lower('property [partial]:\n  (x : nat)\n  c = $(x + 4)\n'
                             '  -- External: x b u\n  -- B: b c\n', [spec])
        model = compile_spec(lowered.source, lowered.config)
        self.assertEqual(model.pre_outputs, ('nat',))
        model = replace(model, external=({'relation': 'External', 'observed_outputs': [0]},))
        replay = compile_replay(model)
        self.assertEqual(replay.projection['External'], [0])
        result = run_bridge('replay', lowered.source,
                            {'pre': model.precondition, 'goal': model.goal,
                             'input': [{'type': 'nat', 'value': 5}],
                             'projection': replay.projection, 'external': list(model.external)},
                            callback=lambda event: {'status': 'returned', 'fresh_id': event['fresh_id'],
                                'outputs': [{'position': 0, 'value': {'type': 'nat', 'value': 6}}]})
        self.assertEqual(result['status'], 'passed')

    def test_constructor_output_patterns_infer_local_witness_types(self):
        spec = self.work / 'constructor.watsup'
        spec.write_text('syntax token\nsyntax token =\n  | BOX nat\n  | OTHER\n'
                        'var n : nat\nrelation External: nat token hint(input %0)\n'
                        'rule External/main: n (BOX n)\n')
        lowered = self.lower('property [pattern]:\n  (x : nat)\n  b = x\n'
                             '  -- External: x (BOX b)\n', [spec])
        model = compile_spec(lowered.source, lowered.config)
        self.assertEqual(model.pre_outputs, ('nat',))
        result = run_bridge('debug', lowered.source,
                            {'pre': model.precondition, 'goal': model.goal,
                             'input': [{'type': 'nat', 'value': 5}]})
        self.assertEqual(result['status'], 'passed')

    def test_equality_infers_both_orientations_and_nested_pattern_witnesses(self):
        for condition in ['x = b', '(b) = x', '(b, c) = (x, x)',
                          '(x, x) = (b, c)']:
            with self.subTest(condition=condition):
                lowered = self.lower('property [binding]:\n  (x : nat)\n  b = x\n'
                                     '  -- ' + condition + '\n')
                model = compile_spec(lowered.source, lowered.config)
                self.assertEqual(model.pre_outputs, ('nat',))
                result = run_bridge('debug', lowered.source,
                                    {'pre': model.precondition, 'goal': model.goal,
                                     'input': [{'type': 'nat', 'value': 5}]})
                self.assertEqual(result['status'], 'passed')

    def test_list_equality_witness_discovery_uses_native_element_types(self):
        lowered = self.lower('property [lists]:\n  (x : nat)\n  b = x\n'
                             '  -- [b] = [x]\n')
        witness = next(internal for internal, public in lowered.source_map['variables'].items()
                       if public == 'b')
        self.assertIn(f'var {witness} : nat', lowered.source.read_text())

    def test_variable_names_do_not_rename_native_type_roles(self):
        spec = self.work / 'types.watsup'
        spec.write_text('syntax token = TOKEN\n'
                        'dec $identity<X>(X) : X\n'
                        'def $identity<X>(X) = X\n')
        lowered = self.lower('property [roles]:\n  (token : nat)\n  true\n'
                             '  -- var local : token\n'
                             '  -- local = $identity<token>(TOKEN)\n', [spec])
        model = compile_spec(lowered.source, lowered.config)
        self.assertEqual([item['type'] for item in model.inputs], ['nat'])
        self.assertEqual(model.pre_outputs, ())
        result = run_bridge('debug', lowered.source,
                            {'pre': model.precondition, 'goal': model.goal,
                             'input': [{'type': 'nat', 'value': 5}]})
        self.assertEqual(result['status'], 'passed')

    def test_comments_before_and_within_conditions_preserve_native_syntax(self):
        for condition in ['(; explanation ;) -- External: x b',
                          '-- External: x b (; explanation\n more explanation ;)',
                          '-- if (\n\n      x = x)\n  -- External: x b']:
            with self.subTest(condition=condition):
                lowered = self.lower('property [comments]:\n  (x : nat)\n  b = $(x + 1)\n  ' + condition + '\n')
                model = compile_spec(lowered.source, lowered.config)
                self.assertEqual(model.pre_outputs, ('nat',))

    def test_blank_condition_lines_preserve_error_line_numbers(self):
        with self.assertRaises(CompileError) as caught:
            self.lower('property [lines]:\n  (x : nat)\n  true\n'
                       '  -- if (\n\n      missing = x)\n')
        self.assertIn('Property.watsup:6.7', str(caught.exception))

    def test_explicit_condition_variable_type_is_local_and_checked(self):
        lowered = self.lower('property [typed_local]:\n  (x : nat)\n  b = $(x + 1)\n'
                             '  -- var b : nat\n  -- External: x b\n')
        model = compile_spec(lowered.source, lowered.config)
        self.assertEqual(model.pre_outputs, ('nat',))

    def test_strings_comments_and_nested_input_types(self):
        lowered = self.lower('property [literal]:\n  (xs : (nat, text))\n'
                             '  "missing -- Fake: z" = "missing -- Fake: z"\n'
                             '  ;; goal mentions no variable z\n')
        model = compile_spec(lowered.source, lowered.config)
        self.assertEqual(len(model.inputs), 1)
        self.assertEqual(model.pre_outputs, ())

    def test_rejects_layout_scope_and_type_errors_at_original_source(self):
        for text, line in [
            ('property [bad]: (x : nat)\n  x = x\n', 1),
            ('property [bad]:\n  (x : nat) x = x\n', 2),
            ('property [bad]:\n  (x : nat)\n  missing = x\n', 3),
            ('property [bad]:\n  (x : text)\n  true\n  -- External: x b\n', 4),
            ('property [bad]:\n  (x : nat)\n  true\n  -- External: b c\n', 4),
            ('property [bad]:\n  ()\n  b = b\n  -- External: 5 b\n', 2),
        ]:
            with self.subTest(text=text):
                with self.assertRaises(CompileError) as caught:
                    self.lower(text)
                self.assertIn(f'Property.watsup:{line}', str(caught.exception))

    def test_ordered_sources_and_specification_errors_keep_original_locations(self):
        first = self.work / 'first.watsup'
        second = self.work / 'second.watsup'
        first.write_text('syntax token = TOKEN\n')
        second.write_text('var t : token\n')
        paths = [first, second]
        original = [p.read_bytes() for p in paths]
        lowered = self.lower('property [ordered]:\n  (t : token)\n  t = t\n', paths)
        self.assertEqual(paths, [first, second])
        self.assertEqual([p.read_bytes() for p in paths], original)
        compile_spec(lowered.source, lowered.config)
        second.write_text('var t : missing\n')
        with self.assertRaises(CompileError) as caught:
            self.lower('property [ordered]:\n  ()\n  true\n', paths)
        self.assertIn(f'{second}:1', str(caught.exception))


if __name__ == '__main__':
    unittest.main()
