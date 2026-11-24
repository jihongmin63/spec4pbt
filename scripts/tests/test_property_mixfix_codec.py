"""Constructor wire identities preserve full SpecTec mixfix shapes."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from scripts.property.bridge import build_bridge
from scripts.property.codec import decode_input
from scripts.property.coq_codec import constructor_schema, render_input_codec
from scripts.property.compiler import compile_debug, compile_spec
from scripts.property.debug import debug
from scripts.property import rocq

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'scripts/tests/fixtures/property/bridge/mixfix_input.watsup'


class MixfixCodecTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = Path(tempfile.mkdtemp(prefix='property-mixfix-codec.',
                                             dir=ROOT / '_opam-testing-theorems/checks'))
        cls.config = cls.directory / 'Property.toml'
        cls.config.write_text('precondition = "Pre"\ngoal = "Goal"\n')
        cls.model = compile_spec(SOURCE, cls.config)

    def values(self):
        cases = self.model.type_schema['token']['constructors']
        other = {'type': 'token', 'constructor': cases[-1]['name'], 'args': []}
        return [{'type': 'token', 'constructor': case['name'], 'args': [
            other if field == 'token' else {'type': field, 'value': '7'}
            for field in case['fields']]} for case in cases]

    def bridge(self, mode, payload):
        result = subprocess.run(['bash', str(ROOT / 'environment/env.sh'), 'frontend',
                                 str(build_bridge()), mode, str(SOURCE)],
                                input=json.dumps(payload) + '\n', capture_output=True,
                                text=True, timeout=90)
        (self.directory / f'{mode}.log').write_text(result.stdout + result.stderr)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return json.loads(result.stdout)

    def test_constructor_ids_are_unique_and_preserve_simple_prefixes(self):
        cases = self.model.type_schema['token']['constructors']
        names = [case['name'] for case in cases]
        self.assertEqual(len(set(names)), len(names), names)
        self.assertEqual(names[-3:], ['PLAIN', 'WRAP', 'OTHER'])
        constructor_schema(self.model.type_schema)
        # Source offsets and constructor ordinals are not part of wire identity.
        shifted = self.directory / 'shifted.watsup'
        shifted.write_text('\n\n' + SOURCE.read_text().replace(
            '  | BOX nat END\n  | BOX nat LEFT', '  | BOX nat LEFT\n  | BOX nat END'))
        reordered = compile_spec(shifted, self.config)
        self.assertEqual(set(names), {case['name'] for case in
                                     reordered.type_schema['token']['constructors']})

    def test_bridge_reconstructs_native_suffix_and_punctuation_matches(self):
        expected = [10, 11, 12, 13, 14, 15, 16, 99, 99]
        for value, number in zip(self.values(), expected):
            with self.subTest(constructor=value['constructor'], output=number):
                result = self.bridge('debug', {'pre': 'Pre', 'goal': 'Goal', 'input': [value]})
                self.assertEqual(result['status'], 'passed')
                self.assertEqual(result['pre_outputs'], [{'type': 'nat', 'value': str(number)}])
        self.assertEqual(self.bridge('codec', self.values()), self.values())

    def test_translated_coq_encoder_roundtrips_every_mixfix_shape(self):
        # Use the actual translator's metadata and constructor symbols. Extraction
        # passes each constructor, including escaped structural IDs, to the bridge.
        run, publication = rocq._generate_property(SOURCE, self.config, inventory=True)
        plan = json.loads((publication / 'PropertyPlan.json').read_text())
        schema = plan['type_schema']
        self.assertEqual(schema, self.model.type_schema)
        declaration = schema['token']
        coq_type = declaration['coq_type']
        cases = declaration['constructors']
        constructors = ['| ' + case['coq_name'] + ' : ' + ' -> '.join(
            [coq_type if typ == 'token' else typ for typ in case['fields']] + [coq_type])
            for case in cases]
        values = ['(' + ' '.join([case['coq_name']] + [
            cases[-1]['coq_name'] if typ == 'token' else '7' for typ in case['fields']]) + ')'
            for case in cases]
        source = 'From QuickChick Require Import QuickChick.\n' + \
            'From Coq Require Import String Ascii ZArith List.\n' + \
            'Import ListNotations.\nOpen Scope string_scope.\n' + \
            f'Inductive {coq_type} : Set :=\n' + '\n'.join(constructors) + '.\n' + \
            f'Record Input := mkInput {{ input_t : {coq_type} }}.\n' + \
            render_input_codec(self.model.inputs, schema) + \
            'Definition values := [' + ';'.join('encode_input (mkInput ' + v + ')' for v in values) + '].\n' + \
            'Extraction "generator.ml" values.\n'
        from scripts.tests.test_property_type_generators import TypeGeneratorTests
        wires = TypeGeneratorTests.extract(self, source, '''let () =
  List.iter (fun value -> List.iter print_char value; print_newline ()) Generator.values
''')
        self.assertEqual([wire['t'] for wire in wires], self.values())
        program = compile_debug(self.model)
        for wire, expected in zip(wires, [10, 11, 12, 13, 14, 15, 16, 99, 99]):
            decode_input(wire, self.model.inputs, constructor_schema(schema))
            result = debug(program, wire)
            self.assertEqual(result.status, 'passed', result.reason)
            self.assertEqual(result.trace['pre_outputs'], [{'type': 'nat', 'value': str(expected)}])


if __name__ == '__main__':
    unittest.main()
