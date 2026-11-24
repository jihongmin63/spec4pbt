"""Exercise automatically rendered type generators through pinned extraction."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.property.codec import CodecError, decode_input
from scripts.property.coq_codec import constructor_schema, render_input_codec, render_type_generators
from scripts.tests.test_property_coq_codec import SCHEMA

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import run as runner

PRELUDE = '''From QuickChick Require Import QuickChick.
From Coq Require Import String Ascii ZArith List.
Import QcDefaultNotation ListNotations.
Open Scope string_scope.
'''


class TypeGeneratorTests(unittest.TestCase):
    def extract(self, source, driver):
        checks = ROOT / '_opam-testing-theorems/checks'
        checks.mkdir(parents=True, exist_ok=True)
        directory = Path(tempfile.mkdtemp(prefix='property-type-generators.', dir=checks))
        (directory / 'Probe.v').write_text(source)
        (directory / 'driver.ml').write_text(driver)

        def command(index, arguments):
            result = subprocess.run(arguments, cwd=directory, capture_output=True,
                                    text=True, timeout=120)
            (directory / f'{index}.log').write_text(result.stdout + result.stderr)
            self.assertEqual(result.returncode, 0,
                             f'{directory}\n{result.stdout}{result.stderr}')
            return result.stdout

        env = ['bash', str(ROOT / 'environment/env.sh')]
        command(0, env + ['coqc', '-q', 'Probe.v'])
        runner.normalize_extraction(directory, 'generator')
        compiler = env + ['ocamlfind', 'ocamlopt', '-package', 'zarith,unix',
                          '-linkpkg', '-rectypes', '-w', '-a']
        command(1, compiler + ['-c', 'generator.mli'])
        command(2, compiler + ['generator.ml', 'driver.ml', '-o', 'sampler'])
        output = command(3, [str(directory / 'sampler')])
        return [json.loads(line) for line in output.splitlines()]

    def test_utf8_boundaries_and_generated_text_survive_extraction(self):
        fields = [{'name': 'message', 'type': 'text'}]
        points = [0, 0x7f, 0x80, 0x7ff, 0x800, 0xd7ff, 0xe000,
                  0xffff, 0x10000, 0x10ffff]
        source = PRELUDE + render_type_generators({}) + '''
Record Input := mkInput { input_message : string }.
''' + render_input_codec(fields, {}) + '''
Definition scalar_json n := encode_input (mkInput (property_utf8_scalar n)).
Definition sample_text_gen size :=
  bindGen (@arbitrarySized string _ size) (fun value => returnGen (mkInput value)).
Extraction "generator.ml" scalar_json sample_text_gen encode_input run.
'''
        driver = '''let print_json value = List.iter print_char value; print_newline ()
let () =
  List.iter (fun n -> print_json (Generator.scalar_json n)) [POINTS];
  let seed = Random.State.make [| 893 |] in
  for index = 0 to 199 do
    let size = index mod 9 in
    print_json (Generator.encode_input (Generator.run (Generator.sample_text_gen size) size seed))
  done
'''.replace('POINTS', '; '.join(map(str, points)))
        values = self.extract(source, driver)
        for point, value in zip(points, values):
            self.assertEqual(value['message']['value'].encode('utf-8'), chr(point).encode('utf-8'))
        samples = values[len(points):]
        self.assertEqual(len(samples), 200)
        self.assertTrue(any(any(ord(char) > 0xffff for char in value['message']['value'])
                            for value in samples))
        for index, value in enumerate(samples):
            decode_input(value, fields)
            text = value['message']['value']
            self.assertLessEqual(len(text), index % 9)
            self.assertTrue(all(not 0xd800 <= ord(char) <= 0xdfff for char in text))

    def test_mutual_adts_with_indirect_base_generate_at_zero_and_positive_sizes(self):
        fields = [{'name': 'left', 'type': 'left'}, {'name': 'right', 'type': 'right'}]
        source = PRELUDE + '''
Inductive CoqTree : Set :=
| CoqLeaf : nat -> Z -> string -> bool -> CoqTree
| CoqNode : CoqTree -> CoqTree -> CoqTree.
Inductive CoqLeft : Set := CoqStop : CoqLeft | CoqLeftNext : CoqRight -> CoqLeft
with CoqRight : Set := CoqRightNext : CoqLeft -> CoqTree -> CoqRight.
''' + render_type_generators(SCHEMA) + '''
Record Input := mkInput { input_left : CoqLeft; input_right : CoqRight }.
Definition sample_input_gen size :=
  bindGen (@arbitrarySized CoqLeft _ size) (fun left =>
  bindGen (@arbitrarySized CoqRight _ size) (fun right => returnGen (mkInput left right))).
''' + render_input_codec(fields, SCHEMA) + '''
Extraction "generator.ml" sample_input_gen encode_input run.
'''
        values = self.extract(source, '''let print_json value = List.iter print_char value; print_newline ()
let () =
  let seed = Random.State.make [| 421 |] in
  for index = 0 to 99 do
    let size = index mod 5 in
    print_json (Generator.encode_input (Generator.run (Generator.sample_input_gen size) size seed))
  done
''')
        self.assertEqual(len(values), 100)
        for index, value in enumerate(values):
            decode_input(value, fields, constructor_schema(SCHEMA))
            self.assertEqual(value['right']['constructor'], 'RIGHT')
            if index % 5 == 0:
                self.assertEqual(value['left']['constructor'], 'STOP')
                self.assertEqual(value['right']['args'][0]['constructor'], 'STOP')
        self.assertTrue(any(value['left']['constructor'] == 'LEFT' for value in values))
        self.assertTrue(any(value['right']['args'][1]['constructor'] == 'NODE' for value in values))

    def test_mutually_declared_acyclic_types_retain_all_constructor_choices(self):
        schema = {
            'wrapper': {'coq_type': 'Wrapper', 'constructors': [
                {'name': 'WRAP', 'coq_name': 'Wrap', 'fields': ['choice']}]},
            'choice': {'coq_type': 'Choice', 'constructors': [
                {'name': str(n), 'coq_name': f'Choice{n}', 'fields': []}
                for n in range(4)]},
        }
        fields = [{'name': 'wrapped', 'type': 'wrapper'}]
        source = PRELUDE + '''
Inductive Wrapper : Set := Wrap : Choice -> Wrapper
with Choice : Set := Choice0 | Choice1 | Choice2 | Choice3.
''' + render_type_generators(schema) + '''
Record Input := mkInput { input_wrapped : Wrapper }.
Definition sample_input_gen size :=
  bindGen (@arbitrarySized Wrapper _ size) (fun value => returnGen (mkInput value)).
''' + render_input_codec(fields, schema) + '''
Extraction "generator.ml" sample_input_gen encode_input run.
'''
        values = self.extract(source, '''let print_json value = List.iter print_char value; print_newline ()
let () =
  let seed = Random.State.make [| 421 |] in
  for index = 0 to 99 do
    let size = index mod 3 in
    print_json (Generator.encode_input (Generator.run (Generator.sample_input_gen size) size seed))
  done
''')
        for value in values:
            decode_input(value, fields, constructor_schema(schema))
        self.assertEqual({value['wrapped']['args'][0]['constructor'] for value in values},
                         {'0', '1', '2', '3'})

    def test_uninhabited_recursive_types_report_a_schema_error(self):
        schema = {'void': {'coq_type': 'Void', 'constructors': [
            {'name': 'LOOP', 'coq_name': 'Loop', 'fields': ['void']}]}}
        with self.assertRaisesRegex(CodecError, 'finite.*void|void.*finite'):
            render_type_generators(schema)


if __name__ == '__main__':
    unittest.main()
