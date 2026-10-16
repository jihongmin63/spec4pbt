"""End-to-end tests: native source -> typed upstream IL -> executable Lean."""
import json
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
TRANSLATOR = ROOT / 'translator' / '_build' / 'default' / 'main.exe'
AE = ROOT / 'external/spectecx/spectec/specs/itpl/ae/spec.spectec'

class TranslationTests(unittest.TestCase):
    def translate(self, source, namespace):
        self.assertTrue(TRANSLATOR.is_file(), 'independent SpecTecX translator executable is missing')
        directory = tempfile.TemporaryDirectory(dir=ROOT / 'translator')
        self.addCleanup(directory.cleanup)
        output = pathlib.Path(directory.name) / 'Generated.lean'
        manifest = output.with_suffix('.json')
        result = subprocess.run([str(TRANSLATOR), '--namespace', namespace,
            '--output', str(output), '--manifest', str(manifest), str(source)],
            cwd=ROOT, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return output, json.loads(manifest.read_text())

    def lean(self, output, assertions):
        with output.open('a') as stream:
            stream.write('\n' + assertions)
        result = subprocess.run(['lake', 'env', 'lean', str(output)], cwd=ROOT,
                                text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def oracle(self, source, relation, inputs, expected):
        reference = ROOT / 'translator/_build/default/tests/reference.exe'
        result = subprocess.run([str(reference), str(source), relation, json.dumps(inputs)],
            cwd=ROOT, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout), expected)

    def test_recursive_native_ae(self):
        output, manifest = self.translate(AE, 'AeSpec')
        self.assertEqual(manifest['relations']['Eval_expr']['inputs'], [0])
        self.oracle(AE, 'Eval_expr', [{'case': 1, 'args': [
            {'case': 0, 'args': [7]}, {'case': 2, 'args': [
                {'case': 0, 'args': [10]}, {'case': 0, 'args': [4]}]}]}], [13])
        self.lean(output, '''
open AeSpec SpecTecExecution
example : runEval_expr 100 (.c1 (.c0 7) (.c2 (.c0 10) (.c0 4))) =
    .done (.success 13) 0 := by decide
example : runEval_expr 1 (.c0 7) = .outOfFuel := by decide
example : AeSpec.Eval_expr (.c0 7) 7 := by
  refine ⟨0, ?_⟩
  exact runEval_sound program (PrimitiveRunner.unavailable program) 100
    (.call (Call.Eval_expr (.c0 7))) 0 (.success 7) 0 (by decide)
#eval (do
  match Lean.fromJson? (Lean.toJson (expr.c0 (-3))) with
  | Except.ok (value : expr) =>
    unless value = expr.c0 (-3) do throw (IO.userError "codec value")
  | Except.error error => throw (IO.userError error) : IO Unit)
''')

    def test_record_outputs(self):
        output, manifest = self.translate(ROOT / 'translator/tests/fixtures/record.spectec', 'RecordSpec')
        self.oracle(ROOT / 'translator/tests/fixtures/record.spectec', 'Eval', [5],
                    [{'VALUE': 6, 'TRACE': 5}])
        self.assertEqual(manifest['types']['result']['kind'], 'record')
        self.assertEqual(manifest['types']['result']['fields']['VALUE']['type'], 'int')
        self.lean(output, '''
open RecordSpec SpecTecExecution
example : runEval 100 5 = .done (.success { VALUE := 6, TRACE := 5 }) 0 := by decide
example : (match Lean.fromJson? (Lean.toJson (result.mk (-2) 9)) with
    | Except.ok (value : result) => decide (value = result.mk (-2) 9)
    | Except.error _ => false) = true := by decide
''')

    def test_ordered_guards_and_otherwise(self):
        output, _ = self.translate(ROOT / 'translator/tests/fixtures/fallback.spectec', 'Fallback')
        for value, expected in [(5, 1), (0, 2), (-1, 99)]:
            self.oracle(ROOT / 'translator/tests/fixtures/fallback.spectec', 'Choose',
                        [value], [expected])
        self.lean(output, """
open Fallback SpecTecExecution
example : runChoose 100 5 = .done (.success 1) 0 := by decide
example : runChoose 100 0 = .done (.success 2) 0 := by decide
example : runChoose 100 (-1) = .done (.success 99) 0 := by decide
example : runPositive 100 0 = .done .unmatch 0 := by decide
example : runTry 100 0 = .done (.success 77) 0 := by decide
example : runTry 100 5 = .done (.success 5) 0 := by decide
example : SpecTecExecution.runEval program (PrimitiveRunner.unavailable program) 100
    (.orElse (.abort "stop") (fun _ => .pure (1 : Int))) 0 =
    .done (.abort "stop") 0 := by decide
example : SpecTecExecution.runEval program (PrimitiveRunner.unavailable program) 100
    (.orElse (.primitive (Call.Choose 5)) (fun _ => .pure 1)) 0 =
    .unsupportedPrimitive := by decide
""")

    def test_natural_negation(self):
        source = ROOT / 'translator/tests/fixtures/natural.spectec'
        output, _ = self.translate(source, 'Natural')
        self.oracle(source, 'Negate', [3], [-3])
        self.lean(output, """
example : Natural.runNegate 100 3 = .done (.success (-3)) 0 := by decide
""")

    def test_same_type_subtype_check_rejected_before_writes(self):
        # SubE means Boolean membership, not a transparent type annotation.
        self.oracle(ROOT / 'translator/tests/fixtures/subtype.spectec',
                    'Check', [False], [True])
        self.reject('subtype.spectec')

    def test_source_type_cannot_shadow_native_integer_semantics(self):
        source = ROOT / 'translator/tests/fixtures/primitive-shadow.spectec'
        output, _ = self.translate(source, 'Shadow')
        self.oracle(source, 'Difference', [0, 1], [-1])
        self.lean(output, '''
example : Shadow.runDifference 100 0 1 = .done (.success (-1)) 0 := by decide
''')

    def test_record_input_pattern(self):
        source = ROOT / 'translator/tests/fixtures/record-input.spectec'
        output, _ = self.translate(source, 'RecordInput')
        self.oracle(source, 'Eval', [{'VALUE': 5, 'TRACE': 2}], [5])
        self.lean(output, '''
example : RecordInput.runEval 100 { VALUE := 5, TRACE := 2 } =
    .done (.success 5) 0 := by decide
''')

    def test_single_constructor_input_pattern(self):
        source = ROOT / 'translator/tests/fixtures/single-variant.spectec'
        output, _ = self.translate(source, 'SingleVariant')
        self.oracle(source, 'Eval', [{'case': 0, 'args': [5]}], [5])
        self.lean(output, '''
example : SingleVariant.runEval 100 (.c0 5) = .done (.success 5) 0 := by decide
''')

    def test_fresh_destinations_are_not_overwritten(self):
        with tempfile.TemporaryDirectory() as directory:
            output = pathlib.Path(directory) / 'Keep.lean'
            output.write_text('keep this')
            manifest = output.with_suffix('.json')
            result = subprocess.run([str(TRANSLATOR), '--namespace', 'Keep',
                '--output', str(output), '--manifest', str(manifest), str(AE)],
                cwd=ROOT, text=True, capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(output.read_text(), 'keep this')
            self.assertFalse(manifest.exists())

    def test_generated_name_collision_rejected_before_writes(self):
        self.reject('collision.spectec')

    def test_partial_arithmetic_rejected_before_writes(self):
        self.reject('division.spectec')

    def reject(self, fixture):
        with tempfile.TemporaryDirectory() as directory:
            output = pathlib.Path(directory) / 'Bad.lean'
            manifest = output.with_suffix('.json')
            result = subprocess.run([str(TRANSLATOR), '--namespace', 'Bad',
                '--output', str(output), '--manifest', str(manifest),
                str(ROOT / 'translator/tests/fixtures' / fixture)],
                cwd=ROOT, text=True, capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('unsupported', result.stderr)
            self.assertFalse(output.exists())
            self.assertFalse(manifest.exists())

if __name__ == '__main__':
    unittest.main()
