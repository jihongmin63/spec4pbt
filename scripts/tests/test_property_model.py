"""Frontend-derived property model and ABI checks."""
from pathlib import Path
import unittest

from scripts.property.compiler import CompileError, compile_spec


ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / 'scripts/tests/fixtures/property/bridge'


class ModelTests(unittest.TestCase):
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
