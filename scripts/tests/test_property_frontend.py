"""Actual SpecTec property parsing and typed output provenance."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from scripts.toolchain import resolve_toolchain, PROPERTY_EXECUTABLE, PROPERTY_RUN_EXECUTABLE

from scripts.tests import ROOT, FIXTURES, ORDERED, SCRATCH
SPEC = """syntax result = { VALUE int, TRACE int }
var n : int
relation Eval: int ~> result
  hint(input %0)
rule Eval/value: n ~> { VALUE $(n + 1), TRACE n }
relation Inst: int ~> int
  hint(input %0)
rule Inst/value: n ~> n
"""
VALUE = """property grows:
  (n : int)
  $(v > n)
  -- Eval: n ~> { VALUE v, TRACE t }
"""
PROGRESS = """property progress:
  (n : int)
  Inst: n ~> s
  -- Eval: n ~> r
"""

class PropertyFrontendTests(unittest.TestCase):
    def run_frontend(self, source, spec=SPEC):
        tool = resolve_toolchain(ROOT)
        exe = tool.root / PROPERTY_EXECUTABLE
        self.assertTrue(exe.is_file(), 'SpecTec property frontend is not implemented')
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root/'spec.watsup').write_text(spec)
            (root/'property.watsup').write_text(source)
            return subprocess.run([str(exe), '--spec', str(root/'spec.watsup'), '--property', str(root/'property.watsup')], text=True, capture_output=True, timeout=60)

    def frontend(self, source, spec=SPEC):
        r = self.run_frontend(source, spec)
        self.assertEqual(r.returncode, 0, r.stderr)
        return json.loads(r.stdout)

    def test_parse_boolean_goal_and_infer_record_outputs(self):
        p = self.frontend(VALUE)['properties'][0]
        self.assertEqual(p['name'], 'grows')
        self.assertEqual(p['inputs'][0]['name'], 'n')
        self.assertEqual(p['inputs'][0]['type']['lean'], 'Int')
        self.assertEqual(p['goal']['kind'], 'guard')
        self.assertEqual(p['conditions'][0]['relation'], 'Eval')
        self.assertEqual(p['conditions'][0]['inputs'], [0])
        self.assertEqual(p['conditions'][0]['arguments'][1]['fields']['VALUE']['name'], 'v')

    def test_goal_relation_outputs_are_typed(self):
        p = self.frontend(PROGRESS)['properties'][0]
        self.assertEqual(p['goal']['relation'], 'Inst')
        self.assertEqual(p['goal']['arguments'][1]['type']['lean'], 'Int')

    def test_multiple_inputs_and_property_scope(self):
        p = self.frontend("""property eq:
 (n : int) (m : int)
 n = m

property eq2:
 (n : int)
 n = n
""")['properties']
        self.assertEqual([len(x['inputs']) for x in p], [2,1])

    def test_duplicate_property_rejected(self):
        r = self.run_frontend("""property a:
 (n : int)
 n = n

property a:
 (n : int)
 n = n
""")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn('duplicate', r.stderr)

    def test_unknown_relation_rejected_with_location(self):
        r = self.run_frontend(PROGRESS.replace('Inst:', 'Missing:'))
        self.assertNotEqual(r.returncode, 0)
        self.assertIn('Missing', r.stderr)
        self.assertIn('property.watsup', r.stderr)

    def test_wrong_input_type_rejected(self):
        r = self.run_frontend(VALUE.replace('(n : int)', '(n : bool)'))
        self.assertNotEqual(r.returncode, 0)

    def test_unknown_input_type_rejected(self):
        r = self.run_frontend(VALUE.replace('(n : int)', '(n : missing)'))
        self.assertNotEqual(r.returncode, 0)

    def test_property_outputs_have_local_types(self):
        p = self.frontend(VALUE, SPEC + "\nvar v : bool\n")['properties'][0]
        self.assertEqual(p['conditions'][0]['arguments'][1]['fields']['VALUE']['type']['lean'], 'Int')

    def test_suffixed_explicit_inputs_keep_independent_types(self):
        p = self.frontend("property suffix:\n (n_0 : int) (n_1 : bool)\n n_1\n")['properties'][0]
        self.assertEqual(p['goal']['expression']['type']['lean'], 'Bool')

    def test_existing_rule_syntax_does_not_become_property(self):
        r = self.run_frontend("""rule Eval/new: 1 ~> { VALUE 2, TRACE 1 }
""")
        self.assertNotEqual(r.returncode, 0)

    def test_helper_relation_and_property_share_one_document(self):
        source = """relation Helper: int ~> int
  hint(input %0)
rule Helper/value: n ~> n
  -- Inst: n ~> n

property helper_value:
  (n : int)
  Helper: n ~> n
"""
        result = self.frontend(source)
        self.assertEqual(result['properties'][0]['goal']['relation'], 'Helper')
        self.assertEqual(result['properties'][0]['goal']['arguments'][1]['type']['lean'], 'Int')
        self.assertEqual(result['properties'][0]['helpers'], [
            {'name':'Helper','rules':[{'dependencies':['Inst']}]}
        ])

    def test_helper_cannot_replace_source_relation(self):
        source = """relation Eval: int ~> int
  hint(input %0)
rule Eval/value: n ~> n

property collision:
  (n : int)
  true
"""
        result = self.run_frontend(source)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Eval', result.stderr)

    def test_helper_rule_cannot_extend_source_relation(self):
        source = """rule Inst/extra: 0 ~> 0

property collision:
  (n : int)
  true
"""
        result = self.run_frontend(source)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Inst', result.stderr)

    def test_negated_zero_output_helper_condition_is_typed(self):
        source = """relation Probe: |- int
  hint(input %0)
rule Probe/value: |- n
  -- Inst: n ~> _

property negative:
  (n : int)
  true
  -- Probe:/ |- n
"""
        clause = self.frontend(source)['properties'][0]
        self.assertEqual(clause['conditions'][0]['kind'], 'not_relation')
        self.assertEqual(clause['conditions'][0]['relation'], 'Probe')

if __name__ == '__main__':
    unittest.main()
