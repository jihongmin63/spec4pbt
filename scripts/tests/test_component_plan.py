"""Structural and Lean-semantic regressions for component contracts."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from scripts.tests import ROOT, SCRATCH
from scripts.toolchain import digest
from scripts.property.component_plan import _validate, check


class ComponentPlanTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='component_plan_', dir=SCRATCH)
        self.addCleanup(self.tmp.cleanup)
        self.directory = Path(self.tmp.name)
        self.module = '.'.join(self.directory.relative_to(ROOT).parts) + '.Contract'
        self.contract_file = self.directory / 'Contract.lean'
        self.contract_file.write_text(f'''import Spec4Pbt.GoalTools
namespace {self.module}
structure Input where
  a : Nat
  b : Nat
def Premise (x : Input) : Prop := x.a = x.b
end {self.module}
''')
        (self.directory / 'spec.watsup').write_text('relation Dummy: nat ~> nat\n')
        (self.directory / 'property.watsup').write_text('property dummy:\n  (n : nat)\n  true\n')
        (self.directory / 'config.toml').write_text('schema_version = 1\nobservations = []\n')
        (self.directory / 'external.toml').write_text('schema_version = 1\nexternal = []\n')
        base = self.directory.relative_to(ROOT).as_posix()
        self.plan = {
            'schema_version': 1,
            'target': {
                'spec': base + '/spec.watsup', 'property': base + '/property.watsup',
                'name': 'dummy', 'config': base + '/config.toml',
                'external': base + '/external.toml', 'type_aliases': {},
                'source_sha256': {base + '/spec.watsup': digest(self.directory / 'spec.watsup')},
                'lean_sha256': {base + '/Contract.lean': digest(self.contract_file)},
            },
            'contract_module': self.module, 'imports': [], 'implementation_refs': [],
            'values': [
                {'id': 'x', 'type': 'Nat'}, {'id': 'y', 'type': 'Nat'},
                {'id': 'z', 'type': 'Nat'}, {'id': 'w', 'type': 'Nat'},
                {'id': 'result', 'type': self.module + '.Input'},
            ],
            'components': [
                {'id': 'left', 'input': [], 'output': ['x'], 'require': 'True',
                 'ensure': 'v_x = 0', 'implementation': None},
                {'id': 'right', 'input': [], 'output': ['y'], 'require': 'True',
                 'ensure': 'v_y = 0', 'implementation': None},
                {'id': 'join', 'input': ['x', 'y'], 'output': ['z'],
                 'require': 'v_x = v_y', 'ensure': 'v_z = v_x', 'implementation': None},
                {'id': 'reuse', 'input': ['x'], 'output': ['w'],
                 'require': 'v_x = 0', 'ensure': 'v_w = v_x', 'implementation': None},
                {'id': 'final', 'input': ['z', 'w'], 'output': ['result'],
                 'require': 'v_z = v_w',
                 'ensure': 'v_result.a = v_z ∧ v_result.b = v_w', 'implementation': None},
            ],
            'connections': [
                {'target': 'left', 'sources': [], 'proof': 'by intros; trivial'},
                {'target': 'right', 'sources': [], 'proof': 'by intros; trivial'},
                {'target': 'join', 'sources': ['left', 'right'],
                 'proof': 'by intros; simp_all [require_join, ensure_left, ensure_right]'},
                {'target': 'reuse', 'sources': ['left'],
                 'proof': 'by intros; simp_all [require_reuse, ensure_left]'},
                {'target': 'final', 'sources': ['join', 'reuse'],
                 'proof': 'by intros; simp_all [require_final, ensure_join, ensure_reuse]'},
            ],
            'final': {'output': 'result',
                      'proof': f'by intros; simp_all [ensure_final, ensure_join, ensure_reuse, {self.module}.Premise]'},
        }
        self.mocks = [patch('scripts.property.component_plan.load_clause', return_value={}),
                      patch('scripts.property.component_plan.compile_clause', return_value={}),
                      patch('scripts.property.component_plan.select_external', return_value={}),
                      patch('scripts.property.component_plan.render_contract', return_value=self.contract_file.read_text())]
        for mock in self.mocks:
            mock.start()
            self.addCleanup(mock.stop)

    def save(self):
        path = self.directory / 'plan.json'
        path.write_text(json.dumps(self.plan))
        return path

    def test_fanin_reuse_and_exact_premise(self):
        result = check(self.save(), timeout_seconds=180)
        self.assertEqual(result['remaining_require'], [])
        self.assertEqual(len(result['components']), 5)

    def test_missing_require_and_ungrounded_cycle(self):
        self.plan['connections'] = [x for x in self.plan['connections'] if x['target'] != 'reuse']
        with self.assertRaisesRegex(ValueError, 'missing requirement discharge'):
            _validate(self.plan, ROOT)
        self.plan['connections'].append({'target': 'reuse', 'sources': ['final'], 'proof': 'by intros; trivial'})
        with self.assertRaisesRegex(ValueError, 'cycle'):
            _validate(self.plan, ROOT)

    def test_resampling_and_type_mismatch(self):
        self.plan['components'][1]['output'] = ['x']
        with self.assertRaisesRegex(ValueError, 'twice'):
            _validate(self.plan, ROOT)
        self.plan['components'][1]['output'] = ['y']
        self.plan['values'][-1]['type'] = 'Nat'
        with self.assertRaisesRegex(ValueError, 'Contract.Input'):
            _validate(self.plan, ROOT)

    def test_lost_correlation_and_omitted_premise_fail_in_lean(self):
        self.plan['connections'][2]['sources'] = ['left']
        with self.assertRaises((ChildProcessError, ValueError)):
            check(self.save(), timeout_seconds=180)
        self.plan['connections'][2]['sources'] = ['left', 'right']
        self.plan['components'][2]['require'] = 'v_x = v_y + 1'
        with self.assertRaises((ChildProcessError, ValueError)):
            check(self.save(), timeout_seconds=180)

    def test_separately_sampled_value_cannot_reuse_a_fact(self):
        self.plan['values'].append({'id': 'xcopy', 'type': 'Nat'})
        self.plan['components'].append({
            'id': 'copy', 'input': [], 'output': ['xcopy'],
            'require': 'True', 'ensure': 'True', 'implementation': None,
        })
        self.plan['connections'].append({
            'target': 'copy', 'sources': [], 'proof': 'by intros; trivial',
        })
        join = self.plan['components'][2]
        join['input'] = ['xcopy', 'y']
        join['require'] = 'v_xcopy = v_y'
        join['ensure'] = 'v_z = v_xcopy'
        with self.assertRaises((ChildProcessError, ValueError)):
            check(self.save(), timeout_seconds=180)
        self.plan['components'][2]['require'] = 'v_x = v_y'
        self.plan['final']['proof'] = 'by intros; trivial'
        with self.assertRaises((ChildProcessError, ValueError)):
            check(self.save(), timeout_seconds=180)

    def test_bogus_missing_and_stale_semantic_source(self):
        self.plan['connections'][2]['proof'] = 'by intros; trivial'
        with self.assertRaises((ChildProcessError, ValueError)):
            check(self.save(), timeout_seconds=180)
        self.plan['connections'][2]['proof'] = ''
        with self.assertRaisesRegex(ValueError, 'nonempty'):
            _validate(self.plan, ROOT)
        self.contract_file.write_text(self.contract_file.read_text().replace('x.a = x.b', 'True'))
        with self.assertRaisesRegex(ValueError, 'stale Lean semantic declaration'):
            _validate(self.plan, ROOT)

    def test_wrong_binding_type_and_sorry_fail(self):
        self.plan['components'][3]['input'] = ['y']
        with self.assertRaises((ChildProcessError, ValueError)):
            check(self.save(), timeout_seconds=180)
        self.plan['components'][3]['input'] = ['x']
        self.plan['values'][0]['type'] = 'Bool'
        with self.assertRaises((ChildProcessError, ValueError)):
            check(self.save(), timeout_seconds=180)
        self.plan['values'][0]['type'] = 'Nat'
        self.plan['connections'][2]['proof'] = 'by sorry'
        with self.assertRaisesRegex(ChildProcessError, 'forbidden axioms'):
            check(self.save(), timeout_seconds=180)

    def test_target_reconstruction_rejects_substitute(self):
        with patch('scripts.property.component_plan.render_contract', return_value='def Premise := True\n'):
            with self.assertRaisesRegex(ValueError, 'does not match original property'):
                _validate(self.plan, ROOT)
        self.plan['imports'] = ['build.scratch.MissingSemanticDeclaration']
        with self.assertRaisesRegex(ValueError, 'missing Lean import'):
            _validate(self.plan, ROOT)


if __name__ == '__main__':
    unittest.main()
