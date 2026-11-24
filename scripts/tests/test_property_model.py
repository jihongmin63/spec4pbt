"""Frontend-derived property model and ABI checks."""
from pathlib import Path
import tempfile
import unittest

from scripts.property.compiler import CompileError, compile_spec


ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / 'scripts/tests/fixtures/property/bridge'


class ModelTests(unittest.TestCase):
    def test_pre_requires_transitive_specification_definitions(self):
        with tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems/checks') as temporary:
            root = Path(temporary)
            source = root / 'missing.watsup'
            source.write_text('''var x : nat
var y : nat
extern relation E: nat nat hint(input %0)
relation H: nat nat hint(input %0)
rule H/main: x y
  -- E: x y
relation Pre: nat nat hint(input %0)
rule Pre/main: x y
  -- H: x y
relation Goal: nat nat hint(input %0 %1)
rule Goal/main: x y
''')
            config = root / 'Property.toml'
            config.write_text('precondition = "Pre"\ngoal = "Goal"\n'
                              '[[external]]\nrelation="E"\nobserved_outputs=[0]\n'
                              'adapter="E"\nconversion="json-v1"\n')
            with self.assertRaisesRegex(CompileError, 'Pre.*specification.*E'):
                compile_spec(source, config)

    def test_direct_property_scope_forms_are_rejected_with_source(self):
        source = FIXTURE.parent / 'observability/scope.watsup'
        cases = [('Negation', 'Test', 'negation'),
                 ('Iteration', 'Test', 'iteration'),
                 ('HigherOrder', 'Test', 'higher_order'),
                 ('Pre', 'Fallback', 'otherwise')]
        for pre, goal, construct in cases:
            with self.subTest(construct=construct):
                directory = Path(tempfile.mkdtemp(dir=ROOT / '_opam-testing-theorems/checks',
                                                  prefix='property-scope-'))
                config = directory / 'Property.toml'
                config.write_text(f'precondition = "{pre}"\ngoal = "{goal}"\n')
                with self.assertRaisesRegex(CompileError, construct + '.*scope.watsup'):
                    compile_spec(source, config)

    def test_input_and_goal_abi_come_from_typed_frontend(self):
        model = compile_spec(FIXTURE / 'partial.watsup', FIXTURE / 'Property.toml')
        self.assertEqual([x['name'] for x in model.inputs], ['x'])
        self.assertEqual([x['type'] for x in model.inputs], ['nat'])
        self.assertEqual(model.pre_outputs, ('nat',))
        self.assertEqual(model.goal_inputs, ('nat', 'nat'))
        self.assertEqual(model.precondition, 'Pre')
        self.assertEqual(model.goal, 'Goal')

    def test_frontend_rejects_unbound_input(self):
        with self.assertRaises(CompileError) as caught:
            compile_spec(FIXTURE / 'unbound.watsup', FIXTURE / 'Property.toml')
        self.assertIn('unbound.watsup', str(caught.exception))


if __name__ == '__main__':
    unittest.main()
