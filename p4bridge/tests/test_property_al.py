"""The native AL lowering keeps source origins and local goal scope."""
import unittest

from p4bridge.tests import test_property_clause as frontend_module

SPEC = frontend_module.SPEC
VALUE = frontend_module.VALUE


class PropertyALTests(unittest.TestCase):
    run_frontend = frontend_module.PropertyFrontendTests.run_frontend
    frontend = frontend_module.PropertyFrontendTests.frontend

    def test_al_bindings_keep_types_and_producer(self):
        clause = self.frontend(VALUE)['properties'][0]
        bindings = clause['condition_blocks'][0]['bindings']
        self.assertEqual({b['name'] for b in bindings}, {'v', 't'})
        self.assertTrue(all(b['producer'] == 'condition.0' for b in bindings))
        self.assertTrue(all(b['type']['key'] == 'int' for b in bindings))

    def test_al_expressions_have_native_node_ids(self):
        clause = self.frontend("property eq:\n (n : int)\n n = n\n")['properties'][0]
        node = clause['goal_block']['nodes'][0]
        self.assertEqual(node['expression']['id'], node['id'] + '/expression')
        self.assertEqual(node['expression']['left']['id'], node['id'] + '/expression/left')

    def test_goal_index_guard_keeps_origin(self):
        source = "property indexed:\n (xs : int*) (i : nat)\n xs[i] = xs[i]\n"
        clause = self.frontend(source)['properties'][0]
        goal = clause['goal_block']
        self.assertGreater(len(goal['nodes']), 1)
        self.assertTrue(all(n['origin'] == 'goal' for n in goal['nodes']))
        self.assertTrue(all(n['scope'] == goal['scope'] for n in goal['nodes']))
        self.assertTrue(any(n['auxiliary'] for n in goal['nodes']))

    def test_goal_output_match_keeps_scope(self):
        source = "property matched:\n (n : int)\n Eval: n ~> { VALUE n, TRACE t }\n"
        clause = self.frontend(source, SPEC)['properties'][0]
        goal = clause['goal_block']
        self.assertGreater(len(goal['nodes']), 1)
        self.assertTrue(all(n['origin'] == 'goal' for n in goal['nodes']))
        self.assertTrue(all(n['scope'] == goal['scope'] for n in goal['nodes']))
        self.assertEqual(goal['nodes'][0]['kind'], 'relation')
        self.assertTrue(any(n['auxiliary'] for n in goal['nodes'][1:]))


if __name__ == '__main__':
    unittest.main()
