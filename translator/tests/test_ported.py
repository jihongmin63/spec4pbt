"""Integration tests for the imported backend on native, elaborated SpecTecX."""
import json
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
TRANSLATOR = ROOT / 'translator/_build/default/main.exe'
REFERENCE = ROOT / 'translator/_build/default/tests/reference.exe'
FIXTURES = ROOT / 'translator/tests/fixtures'


class PortedBackendTests(unittest.TestCase):
    def translate(self, fixture, namespace='Ported', declarative=False, builtin_profile=None):
        self.assertTrue(TRANSLATOR.is_file(), 'build the independent translator first')
        directory = tempfile.TemporaryDirectory(dir=ROOT / 'translator')
        self.addCleanup(directory.cleanup)
        output = pathlib.Path(directory.name) / 'Generated.lean'
        command = [str(TRANSLATOR), '--backend', 'ported', '--namespace', namespace,
                   '--output', str(output)]
        if declarative:
            command.append('--declarative')
        if builtin_profile:
            command.extend(['--builtin-profile', builtin_profile])
        command.append(str(FIXTURES / fixture))
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return output

    def lean(self, output, assertions):
        with output.open('a') as stream:
            stream.write('\n' + assertions)
        result = subprocess.run(['lake', 'env', 'lean', str(output)], cwd=ROOT,
                                text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def oracle(self, fixture, relation, inputs, expected):
        result = subprocess.run([str(REFERENCE), str(FIXTURES / fixture), relation,
                                 json.dumps(inputs)], cwd=ROOT, text=True,
                                capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout), expected)

    def oracle_outcome(self, fixture, relation, inputs, expected):
        result = subprocess.run([str(REFERENCE), str(FIXTURES / fixture), relation,
                                 json.dumps(inputs), '--outcome'], cwd=ROOT,
                                text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout), expected)

    def outcomes(self, output, cases, namespace='Ported'):
        assertions = [f'open {namespace} SpecTecExecution']
        for call, expected in cases:
            assertions.append(f"""
example : runEval specTecExecutableProgram (PrimitiveRunner.unavailable _) 500
    (.call ({call})) 0 = .done (.success ({expected})) 0 := by decide
""")
        self.lean(output, '\n'.join(assertions))

    def test_native_list(self):
        output = self.translate('ported-list.spectec')
        for values in [[], [3, -2, 8]]:
            self.oracle('ported-list.spectec', 'Copy', [values], [values])
        self.outcomes(output, [('SpecTecCall.Copy [3, -2, 8]', '[3, -2, 8]'),
                               ('SpecTecCall.Copy []', '[]')])

    def test_native_options_tuples_and_list_operations(self):
        fixture = 'ported-collections.spectec'
        output = self.translate(fixture)
        self.oracle(fixture, 'CopyOption', [None], [None])
        self.oracle(fixture, 'CopyOption', [{'some': -4}], [{'some': -4}])
        self.oracle(fixture, 'Swap', [[-4, True]], [[True, -4]])
        self.oracle(fixture, 'Append', [[1, 2], [-3]], [[1, 2, -3]])
        self.oracle(fixture, 'Length', [[-3, 7]], [2])
        self.outcomes(output, [
            ('SpecTecCall.CopyOption none', 'none'),
            ('SpecTecCall.CopyOption (some (-4))', 'some (-4)'),
            ('SpecTecCall.Swap (-4, true)', '(true, -4)'),
            ('SpecTecCall.Append [1, 2] [-3]', '[1, 2, -3]'),
            ('SpecTecCall.Length [-3, 7]', '2')])

    def test_polymorphic_functions_type_applications_and_forward_dependencies(self):
        fixture = 'ported-functions.spectec'
        output = self.translate(fixture)
        self.oracle(fixture, 'Compute', [8], [9])
        self.oracle(fixture, 'Apply', [-4], [-3])
        self.oracle(fixture, 'Box', [-4], [{'case': 0, 'args': [-4]}])
        self.oracle(fixture, 'Unbox', [{'case': 0, 'args': [-4]}], [-4])
        self.outcomes(output, [
            ('SpecTecCall.Compute 8', '9'),
            ('SpecTecCall.Apply (-4)', '-3'),
            ('SpecTecCall.Box (-4)', 'box.BOX (-4)'),
            ('SpecTecCall.Unbox (box.BOX (-4))', '-4'),
            ('SpecTecCall.«$identity» Bool true', 'true')])

    def test_iterated_relations_bind_outputs(self):
        fixture = 'ported-iteration.spectec'
        output = self.translate(fixture)
        self.oracle(fixture, 'Add_each', [[1, 2, 3], [10, 20, 30]], [[11, 22, 33]])
        self.oracle(fixture, 'Add_each', [[], []], [[]])
        self.oracle(fixture, 'Add_opt', [{'some': 4}, {'some': 8}], [{'some': 12}])
        self.oracle(fixture, 'Add_opt', [None, None], [None])
        self.outcomes(output, [
            ('SpecTecCall.Add_each [1, 2, 3] [10, 20, 30]', '[11, 22, 33]'),
            ('SpecTecCall.Add_each [] []', '[]'),
            ('SpecTecCall.Add_opt (some 4) (some 8)', 'some 12'),
            ('SpecTecCall.Add_opt none none', 'none')])

    def test_mismatched_iteration_inputs_do_not_succeed(self):
        fixture = 'ported-iteration.spectec'
        output = self.translate(fixture)
        self.oracle_outcome(fixture, 'Add_each', [[1, 2], [10]], {'status': 'unmatch'})
        self.oracle_outcome(fixture, 'Add_opt', [None, {'some': 2}], {'status': 'unmatch'})
        self.lean(output, """
open Ported SpecTecExecution
example : runEval specTecExecutableProgram (PrimitiveRunner.unavailable _) 500
    (.call (SpecTecCall.Add_each [1, 2] [10])) 0 = .done .unmatch 0 := by decide
example : runEval specTecExecutableProgram (PrimitiveRunner.unavailable _) 500
    (.call (SpecTecCall.Add_opt none (some 2))) 0 = .done .unmatch 0 := by decide
""")

    def test_subtype_membership_and_narrowing(self):
        fixture = 'ported-subtype.spectec'
        output = self.translate(fixture)
        for value, member, narrowed in [(-3, False, 99), (0, True, 0), (7, True, 7)]:
            self.oracle(fixture, 'Natural', [value], [member])
            self.oracle(fixture, 'Narrow', [value], [narrowed])
        self.oracle(fixture, 'IsDog', [{'case': 0, 'args': [5]}], [True])
        self.oracle(fixture, 'IsDog', [{'case': 1, 'args': [8]}], [False])
        self.oracle(fixture, 'DogNumber', [{'case': 0, 'args': [5]}], [5])
        self.oracle(fixture, 'DogNumber', [{'case': 1, 'args': [8]}], [0])
        dog = {'case': 0, 'args': [5]}
        cat = {'case': 1, 'args': [8]}
        self.oracle(fixture, 'ListDogs', [[dog, dog]], [2])
        self.oracle(fixture, 'ListDogs', [[dog, cat]], [99])
        self.oracle(fixture, 'ListDogs', [[]], [0])
        self.oracle(fixture, 'TupleDog', [[2, dog]], [7])
        self.oracle(fixture, 'TupleDog', [[-2, dog]], [99])
        self.oracle(fixture, 'TupleDog', [[2, cat]], [99])
        self.oracle(fixture, 'OptionDog', [{'some': dog}], [{'some': dog}])
        self.oracle(fixture, 'OptionDog', [{'some': cat}], [None])
        self.oracle(fixture, 'OptionDog', [None], [None])
        self.outcomes(output, [
            ('SpecTecCall.Natural (-3)', 'false'),
            ('SpecTecCall.Natural 7', 'true'),
            ('SpecTecCall.Narrow (-3)', '99'),
            ('SpecTecCall.Narrow 0', '0'),
            ('SpecTecCall.Narrow 7', '7'),
            ('SpecTecCall.IsDog (animal.DOG 5)', 'true'),
            ('SpecTecCall.IsDog (animal.CAT 8)', 'false'),
            ('SpecTecCall.DogNumber (animal.DOG 5)', '5'),
            ('SpecTecCall.DogNumber (animal.CAT 8)', '0'),
            ('SpecTecCall.ListDogs [animal.DOG 5, animal.DOG 5]', '2'),
            ('SpecTecCall.ListDogs [animal.DOG 5, animal.CAT 8]', '99'),
            ('SpecTecCall.ListDogs []', '0'),
            ('SpecTecCall.TupleDog (2, animal.DOG 5)', '7'),
            ('SpecTecCall.TupleDog (-2, animal.DOG 5)', '99'),
            ('SpecTecCall.TupleDog (2, animal.CAT 8)', '99'),
            ('SpecTecCall.OptionDog (some (animal.DOG 5))', 'some (dog.DOG 5)'),
            ('SpecTecCall.OptionDog (some (animal.CAT 8))', 'none'),
            ('SpecTecCall.OptionDog none', 'none')])

    def test_mutually_recursive_types_and_recursive_relation(self):
        fixture = 'ported-recursive.spectec'
        output = self.translate(fixture)
        leaf = {'case': 0, 'args': [5]}
        nested = {'case': 1, 'args': [{'case': 0, 'args': [leaf]}]}
        self.oracle(fixture, 'Leaf', [leaf], [5])
        self.oracle(fixture, 'Leaf', [nested], [5])
        self.outcomes(output, [
            ('SpecTecCall.Leaf (tree.LEAF 5)', '5'),
            ('SpecTecCall.Leaf (tree.NODE (branch.BRANCH (tree.LEAF 5)))', '5')])
        self.lean(output, """
example : Ported.tree.NODE (Ported.branch.BRANCH (Ported.tree.LEAF 5)) ≠
    Ported.tree.LEAF 5 := by decide
""")

    def test_holds_and_not_holds_premises(self):
        fixture = 'ported-assertions.spectec'
        output = self.translate(fixture)
        for value, positive in [(0, False), (3, True)]:
            self.oracle(fixture, 'Check', [value], [positive])
            self.oracle(fixture, 'NotPositive', [value], [not positive])
        self.outcomes(output, [
            ('SpecTecCall.Check 0', 'false'),
            ('SpecTecCall.Check 3', 'true'),
            ('SpecTecCall.NotPositive 0', 'true'),
            ('SpecTecCall.NotPositive 3', 'false')])

    def test_explicit_donor_builtins_execute_without_target_runtime(self):
        # The target-independent upstream oracle intentionally has no builtin
        # implementations. Verify the donor's admitted builtin lowering in Lean.
        output = self.translate('ported-builtins.spectec', builtin_profile='donor')
        self.outcomes(output, [
            ('SpecTecCall.Sum [1, 2, -4]', '-1'),
            ('SpecTecCall.Sum []', '0'),
            ('SpecTecCall.Reverse [1, -2, 3]', '[3, -2, 1]'),
            ('SpecTecCall.Reverse []', '[]')])

    def test_builtin_meanings_require_explicit_profile(self):
        with tempfile.TemporaryDirectory() as directory:
            output = pathlib.Path(directory) / 'Bad.lean'
            result = subprocess.run([str(TRANSLATOR), '--backend', 'ported',
                '--namespace', 'Ported', '--output', str(output),
                str(FIXTURES / 'ported-builtins.spectec')], cwd=ROOT,
                capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('builtin', result.stderr)
            self.assertFalse(output.exists())

    def test_arithmetic_and_boolean_logic(self):
        fixture = 'ported-arithmetic.spectec'
        output = self.translate(fixture)
        self.oracle(fixture, 'Compute', [2, 5], [-21])
        for inputs, expected in [([2, 5, False], True), ([2, 5, True], False),
                                 ([5, 2, False], False)]:
            self.oracle(fixture, 'Logic', inputs, [expected])
        self.outcomes(output, [
            ('SpecTecCall.Compute 2 5', '-21'),
            ('SpecTecCall.Logic 2 5 false', 'true'),
            ('SpecTecCall.Logic 2 5 true', 'false'),
            ('SpecTecCall.Logic 5 2 false', 'false')])

    def test_partial_arithmetic_aborts_without_taking_fallback(self):
        fixture = 'ported-partial.spectec'
        output = self.translate(fixture)
        for relation, inputs, expected in [
                ('Subtract', [4, 2], 2), ('Subtract', [2, 2], 0),
                ('Divide', [6, 2], 3), ('Divide', [-6, 2], -3),
                ('Divide', [6, -2], -3)]:
            self.oracle(fixture, relation, inputs, [expected])
        # The pinned interpreter asserts on undefined arithmetic. The port
        # represents that failure explicitly as an abort; neither may fallback.
        invalid = [('Subtract', [1, 2]), ('Divide', [5, 2]),
                   ('Divide', [-5, 2]), ('Divide', [6, 0])]
        for relation, inputs in invalid:
            self.oracle_outcome(fixture, relation, inputs, {'status': 'exception'})
        assertions = ['open Ported SpecTecExecution']
        for call in ['SpecTecCall.Subtract 1 2', 'SpecTecCall.Divide 5 2',
                     'SpecTecCall.Divide (-5) 2', 'SpecTecCall.Divide 6 0']:
            assertions.append(f"""
example : (match runEval specTecExecutableProgram (PrimitiveRunner.unavailable _) 500
    (.call ({call})) 0 with
    | .done (.abort _) 0 => true
    | _ => false) = true := by decide
""")
        self.lean(output, '\n'.join(assertions))
        self.outcomes(output, [
            ('SpecTecCall.Subtract 4 2', '2'),
            ('SpecTecCall.Subtract 2 2', '0'),
            ('SpecTecCall.Divide 6 2', '3'),
            ('SpecTecCall.Divide (-6) 2', '-3'),
            ('SpecTecCall.Divide 6 (-2)', '-3')])

    def test_ordered_rule_fallback(self):
        fixture = 'fallback.spectec'
        output = self.translate(fixture)
        for value, expected in [(5, 1), (0, 2), (-1, 99)]:
            self.oracle(fixture, 'Choose', [value], [expected])
        for value, expected in [(0, 77), (5, 5)]:
            self.oracle(fixture, 'Try', [value], [expected])
        self.outcomes(output, [
            ('SpecTecCall.Choose 5', '1'),
            ('SpecTecCall.Choose 0', '2'),
            ('SpecTecCall.Choose (-1)', '99'),
            ('SpecTecCall.Try 0', '77'),
            ('SpecTecCall.Try 5', '5')])

    def test_declarative_output(self):
        output = self.translate('ported-list.spectec', namespace='Ported.Declarative',
                                declarative=True)
        self.assertIn('inductive Copy', output.read_text())
        self.assertNotIn('specTecExecutableProgram', output.read_text())
        self.lean(output, """
example : Ported.Declarative.Copy [1, 2] [1, 2] := by constructor
""")

    def test_declarative_polymorphic_functions(self):
        output = self.translate('ported-functions.spectec', declarative=True)
        self.lean(output, """
open Ported
example : «$identity» true true := by constructor
example : Compute 8 9 := by
  apply Compute.rule
  exact «$earlier».case_1 8 9 8 («$identity».case_1 8) («$later».case_1 8)
example : Box (-4) (box.BOX (-4)) := by
  exact Box.rule (-4) (-4) («$identity».case_1 (-4))
""")

    def test_declarative_fallback_rejected_before_writes(self):
        with tempfile.TemporaryDirectory() as directory:
            output = pathlib.Path(directory) / 'Bad.lean'
            result = subprocess.run([str(TRANSLATOR), '--backend', 'ported',
                '--declarative', '--namespace', 'Ported', '--output', str(output),
                str(FIXTURES / 'fallback.spectec')], cwd=ROOT,
                text=True, capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('does not support declarative otherwise', result.stderr.lower())
            self.assertFalse(output.exists())

    def test_manifest_rejected_before_writes(self):
        with tempfile.TemporaryDirectory() as directory:
            output = pathlib.Path(directory) / 'Generated.lean'
            manifest = output.with_suffix('.json')
            result = subprocess.run([str(TRANSLATOR), '--backend', 'ported',
                '--namespace', 'Ported', '--output', str(output), '--manifest',
                str(manifest), str(FIXTURES / 'ported-list.spectec')], cwd=ROOT,
                text=True, capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('manifest', result.stderr.lower())
            self.assertFalse(output.exists())
            self.assertFalse(manifest.exists())

    def test_fresh_output_not_overwritten(self):
        with tempfile.TemporaryDirectory() as directory:
            output = pathlib.Path(directory) / 'Keep.lean'
            output.write_text('keep this')
            result = subprocess.run([str(TRANSLATOR), '--backend', 'ported',
                '--namespace', 'Ported', '--output', str(output),
                str(FIXTURES / 'ported-list.spectec')], cwd=ROOT,
                text=True, capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(output.read_text(), 'keep this')


if __name__ == '__main__':
    unittest.main()
