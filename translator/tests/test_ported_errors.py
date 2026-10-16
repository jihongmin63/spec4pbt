"""Check runtime aborts remain distinct from rule mismatch and fallback."""
import json
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
TRANSLATOR = ROOT / 'translator/_build/default/main.exe'
REFERENCE = ROOT / 'translator/_build/default/tests/reference.exe'
FIXTURE = ROOT / 'translator/tests/fixtures/error-collections.spectec'


class PartialOperationTests(unittest.TestCase):
    def check(self, relation, inputs, call, expected=None):
        oracle = subprocess.run([str(REFERENCE), str(FIXTURE), relation,
                                 json.dumps(inputs), '--outcome'], cwd=ROOT,
                                text=True, capture_output=True)
        self.assertEqual(oracle.returncode, 0, oracle.stdout + oracle.stderr)
        if expected is None:
            self.assertEqual(json.loads(oracle.stdout), {'status': 'abort'})
            assertion = f"""
example : (match runEval specTecExecutableProgram (PrimitiveRunner.unavailable _) 500
    (.call ({call})) 0 with
    | .done (.abort _) 0 => true
    | _ => false) = true := by decide
"""
        else:
            json_result, lean_result = expected
            self.assertEqual(json.loads(oracle.stdout),
                             {'status': 'success', 'values': [json_result]})
            assertion = f"""
example : runEval specTecExecutableProgram (PrimitiveRunner.unavailable _) 500
    (.call ({call})) 0 = .done (.success ({lean_result})) 0 := by decide
"""
        with tempfile.TemporaryDirectory(dir=ROOT / 'translator') as directory:
            output = pathlib.Path(directory) / 'Errors.lean'
            generated = subprocess.run([str(TRANSLATOR), '--backend', 'ported',
                '--namespace', 'PartialErrors', '--output', str(output), str(FIXTURE)],
                cwd=ROOT, text=True, capture_output=True)
            self.assertEqual(generated.returncode, 0, generated.stdout + generated.stderr)
            with output.open('a') as stream:
                stream.write('\nopen PartialErrors SpecTecExecution\n' + assertion)
            checked = subprocess.run(['lake', 'env', 'lean', str(output)], cwd=ROOT,
                                     text=True, capture_output=True)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_list_index_out_of_bounds_aborts_before_fallback(self):
        for values, index in [([], 0), ([7], 1), ([7], 5)]:
            with self.subTest(values=values, index=index):
                self.check('ListIndex', [values, index],
                           f'SpecTecCall.ListIndex {values} {index}')

    def test_slice_and_update_errors_abort_before_fallback(self):
        for relation, inputs, call in [
            ('ListSlice', [[7], 1, 1], 'SpecTecCall.ListSlice [7] 1 1'),
            ('ListSlice', [[7], 2, 0], 'SpecTecCall.ListSlice [7] 2 0'),
            ('ListUpdate', [[], 0, 9], 'SpecTecCall.ListUpdate [] 0 9'),
            ('ListUpdate', [[7], 1, 9], 'SpecTecCall.ListUpdate [7] 1 9'),
        ]:
            with self.subTest(relation=relation, inputs=inputs):
                self.check(relation, inputs, call)

    def test_valid_collection_boundaries_preserve_results(self):
        for relation, inputs, call, expected in [
            ('ListIndex', [[7], 0], 'SpecTecCall.ListIndex [7] 0', (7, '7')),
            ('ListSlice', [[7], 1, 0], 'SpecTecCall.ListSlice [7] 1 0', ([], '[]')),
            ('ListUpdate', [[7], 0, 9], 'SpecTecCall.ListUpdate [7] 0 9', ([9], '[9]')),
        ]:
            with self.subTest(relation=relation, inputs=inputs):
                self.check(relation, inputs, call, expected)


class TextByteOperationTests(unittest.TestCase):
    def test_byte_fragments_are_rejected_before_output_is_written(self):
        # Native text is bytes: slicing a valid Unicode input can yield a byte
        # fragment that Lean String cannot represent. Even a surrounding length
        # operation must not silently turn that valid native result into abort.
        cases = [
            ('index', 'FirstByteLength', ['é', 0], 1),
            ('slice', 'ByteSliceLength', ['é', 0, 1], 1),
            ('update', 'UpdatedByteLength', ['é', 0, 'x'], 2),
        ]
        for operation, relation, inputs, result in cases:
            with self.subTest(operation=operation):
                fixture = ROOT / f'translator/tests/fixtures/error-text-{operation}.spectec'
                oracle = subprocess.run([str(REFERENCE), str(fixture), relation,
                                         json.dumps(inputs), '--outcome'], cwd=ROOT,
                                        text=True, capture_output=True)
                self.assertEqual(oracle.returncode, 0, oracle.stdout + oracle.stderr)
                self.assertEqual(json.loads(oracle.stdout),
                                 {'status': 'success', 'values': [result]})
                with tempfile.TemporaryDirectory(dir=ROOT / 'translator') as directory:
                    output = pathlib.Path(directory) / 'Text.lean'
                    translated = subprocess.run([str(TRANSLATOR), '--backend', 'ported',
                        '--namespace', 'TextBytes', '--output', str(output), str(fixture)],
                        cwd=ROOT, text=True, capture_output=True)
                    self.assertNotEqual(translated.returncode, 0)
                    self.assertIn('UTF-8', translated.stderr)
                    self.assertFalse(output.exists())


class NamespaceKeywordTests(unittest.TestCase):
    def test_reserved_namespace_components_rejected_before_writing(self):
        fixture = ROOT / 'translator/tests/fixtures/natural.spectec'
        for namespace in ['section', 'Nested.section', 'local', 'meta', 'termination_by']:
            with self.subTest(namespace=namespace):
                with tempfile.TemporaryDirectory(dir=ROOT / 'translator') as directory:
                    output = pathlib.Path(directory) / 'Keyword.lean'
                    translated = subprocess.run([str(TRANSLATOR), '--backend', 'ported',
                        '--namespace', namespace, '--output', str(output), str(fixture)],
                        cwd=ROOT, text=True, capture_output=True)
                    self.assertNotEqual(translated.returncode, 0)
                    self.assertIn('invalid Lean namespace', translated.stderr)
                    self.assertFalse(output.exists())

    def test_reserved_source_identifiers_are_quoted(self):
        with tempfile.TemporaryDirectory(dir=ROOT / 'translator') as directory:
            fixture = pathlib.Path(directory) / 'Keyword.spectec'
            fixture.write_text("""var section : nat
relation Identity: nat ==> nat hint(input %0)
rule Identity: section ==> section
""")
            output = pathlib.Path(directory) / 'Keyword.lean'
            translated = subprocess.run([str(TRANSLATOR), '--backend', 'ported',
                '--namespace', 'KeywordEscaping', '--output', str(output), str(fixture)],
                cwd=ROOT, text=True, capture_output=True)
            self.assertEqual(translated.returncode, 0, translated.stdout + translated.stderr)
            self.assertIn('«section»', output.read_text())
            checked = subprocess.run(['lake', 'env', 'lean', str(output)], cwd=ROOT,
                                     text=True, capture_output=True)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)


if __name__ == '__main__':
    unittest.main()
