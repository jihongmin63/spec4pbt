"""Regressions for the source-aware, nested Wasm Module_ok planning graph."""
from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest

from scripts.property.component_plan import _validate, check, format_text
from scripts.tests import ROOT, SCRATCH


PLAN = ROOT / 'properties/wasm_module_ok/component-plan.json'


class FineWasmPlanTests(unittest.TestCase):
    def setUp(self):
        self.plan = deepcopy(json.loads(PLAN.read_text()))

    def component(self, name):
        return next(item for item in self.plan['components'] if item['id'] == name)

    def connection(self, name):
        return next(item for item in self.plan['connections'] if item['target'] == name)

    def save(self):
        tmp = tempfile.TemporaryDirectory(prefix='fine_wasm_plan_', dir=SCRATCH)
        self.addCleanup(tmp.cleanup)
        path = Path(tmp.name) / 'plan.json'
        path.write_text(json.dumps(self.plan, ensure_ascii=False))
        return path

    def test_real_fine_graph_and_typed_recursive_step(self):
        result = check(PLAN, timeout_seconds=900)
        self.assertEqual(result['remaining_require'], [])
        self.assertEqual(len(result['nodes']), 18)
        self.assertEqual(len(result['edges']), 52)
        self.assertEqual(len(result['execution']['frames']), 5)
        self.assertEqual(len(result['execution']['loops']), 12)
        self.assertEqual(result['templates'][0]['applies_to'], 'function_list')
        self.assertIn('typed recursive templates:', format_text(result))
        self.assertIn('SpecTec.«Module_ok» input.«m»', (ROOT / 'properties/wasm_module_ok/PlanReference/Contract.lean').read_text())

    def test_missing_and_wrong_source_calls_fail_at_site(self):
        site = self.component('tables')['implementation']['site']
        site['fragment'] = 'ConstructiveModuleTables.generate ts.after ts.env'
        with self.assertRaisesRegex(ValueError, 'ConstructiveModulePrelude.lean:generate source fragment'):
            _validate(self.plan, ROOT)
        site['fragment'] = 'ConstructiveModuleTables.generate (boundedContext p) (boundedEnv p)'
        site['owner'] = 'prefixGen'
        self.component('tables')['implementation']['symbol'] = 'prefixGen'
        with self.assertRaisesRegex(ValueError, 'source fragment'):
            _validate(self.plan, ROOT)

    def test_wrong_result_field_and_stale_source_fail(self):
        self.component('types')['implementation']['site']['projections']['ctx_types'] = 'ts.unknown'
        with self.assertRaisesRegex(ValueError, 'not a declared result field'):
            _validate(self.plan, ROOT)
        self.component('types')['implementation']['site']['projections']['ctx_types'] = 'ts.after'
        self.component('types')['implementation']['site']['result']['sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'stale or missing source result structure'):
            _validate(self.plan, ROOT)

    def test_old_free_context_and_assembly_boundary_mappings_fail(self):
        self.plan['values'].append({'id': 'other_free', 'type': 'SpecTec.free'})
        context = self.component('final_context')
        context['output'].append('other_free')
        context['implementation']['site']['projections']['other_free'] = 'ConstructiveFreeModule.moduleFree (raw p)'
        with self.assertRaisesRegex(ValueError, 'pure expression must have one projected output'):
            _validate(self.plan, ROOT)
        self.plan = deepcopy(json.loads(PLAN.read_text()))
        assembly = self.component('assembly')
        assembly['implementation']['symbol'] = 'generate'
        assembly['implementation']['site']['owner'] = 'generate'
        with self.assertRaisesRegex(ValueError, 'source fragment is missing'):
            _validate(self.plan, ROOT)

    def test_coarse_source_mapping_cannot_claim_checked_correspondence(self):
        del self.plan['execution']
        del self.plan['templates']
        self.plan['schema_version'] = 1
        for component in self.plan['components']:
            del component['implementation']['site']
        with self.assertRaisesRegex(ValueError, 'schema 1 cannot claim implementation correspondence'):
            _validate(self.plan, ROOT)

    def test_missing_value_edge_and_wrong_direct_binding_fail(self):
        self.connection('memories')['sources'].remove('tables')
        with self.assertRaisesRegex(ValueError, 'missing value-dependency edges'):
            _validate(self.plan, ROOT)
        self.connection('memories')['sources'].append('tables')
        self.component('memories')['implementation']['site']['uses']['ctx_tables'] = 'ms.after'
        with self.assertRaisesRegex(ValueError, 'input ctx_tables is absent'):
            _validate(self.plan, ROOT)

    def test_nested_coverage_and_decreasing_tail_fail(self):
        frames = self.plan['execution']['frames']
        next(f for f in frames if f['id'] == 'prelude_generate')['members'].remove('exports')
        with self.assertRaisesRegex(ValueError, 'nesting does not cover'):
            _validate(self.plan, ROOT)
        next(f for f in frames if f['id'] == 'prelude_generate')['members'].append('exports')
        loop = next(l for l in self.plan['execution']['loops'] if l['id'] == 'function_bodies')
        loop['smaller'] = 'generate c env (x::xs)'
        with self.assertRaisesRegex(ValueError, 'smaller branch'):
            _validate(self.plan, ROOT)

    def test_parent_result_binding_order_is_checked(self):
        binding = self.plan['execution']['bindings'][2]
        binding['fragment'] = 'pure ⟨p,s,fs⟩'
        with self.assertRaisesRegex(ValueError, 'ConstructiveModuleGeneration.lean:generate execution fragment is missing'):
            _validate(self.plan, ROOT)

    def test_export_wrapper_and_unbounded_count_are_checked(self):
        loop = next(l for l in self.plan['execution']['loops'] if l['id'] == 'export_entries')
        loop['via']['fragment'] = 'ConstructiveExports.descriptors c'
        with self.assertRaisesRegex(ValueError, 'execution fragment is missing'):
            _validate(self.plan, ROOT)
        self.plan = deepcopy(json.loads(PLAN.read_text()))
        loop = next(l for l in self.plan['execution']['loops'] if l['id'] == 'export_entries')
        loop['smaller'] = 'exactCount head tail (n + 1)'
        with self.assertRaisesRegex(ValueError, 'smaller branch'):
            _validate(self.plan, ROOT)

    def test_unrelated_recursive_entry_and_duplicate_sampler_fail(self):
        loop = next(l for l in self.plan['execution']['loops'] if l['id'] == 'function_bodies')
        loop['entry'] = deepcopy(next(l for l in self.plan['execution']['loops'] if l['id'] == 'tables')['entry'])
        with self.assertRaisesRegex(ValueError, 'recursive entry is not called'):
            _validate(self.plan, ROOT)
        self.plan = deepcopy(json.loads(PLAN.read_text()))
        duplicate = deepcopy(self.component('tables')['implementation'])
        duplicate['site']['uses'] = {'ctx_tables': '(boundedContext p)'}
        duplicate['site']['conditions'] = ['ctx_bounded']
        duplicate['site']['projections'] = {'memories': 'ts.items', 'ctx_memories': 'ts.after'}
        self.component('memories')['implementation'] = duplicate
        with self.assertRaisesRegex(ValueError, 'duplicates a source'):
            _validate(self.plan, ROOT)

    def test_recursive_template_source_and_contract_fail(self):
        template = self.plan['templates'][0]
        tail = next(c for c in template['components'] if c['id'] == 'recursive_tail')
        tail['source']['fragment'] = 'done c'
        with self.assertRaisesRegex(ValueError, 'recursive source does not match'):
            _validate(self.plan, ROOT)
        tail['source']['fragment'] = 'generate c env xs (fun y hy => hr y (by simp [hy]))'
        cons = next(c for c in template['components'] if c['id'] == 'cons')
        cons['require'] = 'v_head_func.FTYPE = v_head + 1 ∧ v_tail_funcs.map (·.FTYPE) = v_rest_headers'
        with self.assertRaises((ChildProcessError, ValueError)):
            check(self.save(), timeout_seconds=900)

    def test_lost_section_ensure_fails_lean_discharge(self):
        self.component('tables')['ensure'] = 'True'
        with self.assertRaisesRegex(ValueError, 'plan semantic failure at connection memories'):
            check(self.save(), timeout_seconds=900)

    def test_omitted_raw_section_fact_fails_final_join(self):
        raw = self.component('raw')
        raw['ensure'] = raw['ensure'].replace('v_raw.TYPES = v_types ∧ ', '')
        with self.assertRaisesRegex(ValueError, 'plan semantic failure at connection assembly'):
            check(self.save(), timeout_seconds=900)


if __name__ == '__main__':
    unittest.main()
