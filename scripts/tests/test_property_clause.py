"""Property clauses exercise the real frontend, Lean and external subprocesses."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from scripts.toolchain import resolve_toolchain, PROPERTY_EXECUTABLE, PROPERTY_RUN_EXECUTABLE
from scripts.tests.test_property_frontend import SPEC, VALUE, PROGRESS

from scripts.tests import ROOT, FIXTURES, ORDERED, SCRATCH
CONFIG = {'schema_version': 1, 'observations': [
    {'id': 'value', 'relation': 'Eval', 'observe': ['%1.VALUE']},
    {'id': 'inst', 'relation': 'Inst', 'observe': []}],
    }

def frontend(source, spec=SPEC):
    tool=resolve_toolchain(ROOT)
    exe=tool.root / PROPERTY_EXECUTABLE
    with tempfile.TemporaryDirectory() as tmp:
        p=Path(tmp); (p/'spec.watsup').write_text(spec); (p/'property.watsup').write_text(source)
        r=subprocess.run([str(exe),'--spec',str(p/'spec.watsup'),'--property',str(p/'property.watsup')], capture_output=True,text=True,timeout=60)
        if r.returncode: raise ValueError(r.stderr)
        return json.loads(r.stdout)['properties'][0]

class PropertyPlanTests(unittest.TestCase):
    def test_helper_external_classification_ignores_observation_outputs(self):
        from scripts.property.plan import classify_relations
        helpers = [
            {'name':'First','rules':[{'dependencies':['Primitive']}]},
            {'name':'Second','rules':[{'dependencies':['First']}]},
        ]
        seen = classify_relations(helpers, {'Primitive'})
        self.assertEqual(seen['external'], ['First', 'Primitive', 'Second'])
        self.assertEqual(seen['reasons']['Second'], ['First'])
        self.assertEqual(classify_relations(helpers, {'Primitive'}, observations={'Primitive':['%1']})['external'],
                         seen['external'])

    def test_helper_scc_requires_all_outside_dependencies_external(self):
        from scripts.property.plan import classify_relations
        helpers = [
            {'name':'A','rules':[{'dependencies':['B']}]},
            {'name':'B','rules':[{'dependencies':['A','Primitive']}]},
            {'name':'C','rules':[{'dependencies':['A','Internal']}]},
            {'name':'D','rules':[{'dependencies':['C']}]},
        ]
        seen = classify_relations(helpers, {'Primitive'})
        self.assertEqual(seen['external'], ['A','B','Primitive'])
        self.assertEqual(seen['internal']['C'], ['Internal'])
        self.assertEqual(seen['internal']['D'], ['C'])

    def test_plan_reports_external_helper_and_execution_gap(self):
        source = '''relation Helper: int ~> int
  hint(input %0)
rule Helper/value: n ~> n
  -- Inst: n ~> n

property helper_goal:
  (n : int)
  Helper: n ~> v
'''
        plan = self.compile(source, {'schema_version':1,'observations':[
            {'id':'inst','relation':'Inst','observe':[]}]})
        self.assertEqual(plan['external_relations'], ['Helper','Inst'])
        self.assertEqual(plan['unsupported'][0]['relation'], 'Helper')

    def test_zero_output_wrapper_calls_primitive_relation(self):
        source = '''relation Probe: |- int
  hint(input %0)
rule Probe/value: |- n
  -- Inst: n ~> _

property probe:
  (n : int)
  Probe: |- n
'''
        plan = self.compile(source, {'schema_version':1,'observations':[
            {'id':'inst','relation':'Inst','observe':[]}]})
        self.assertEqual(plan['unsupported'], [])
        self.assertEqual([(call['id'],call['relation'],call['source_relation'])
                          for call in plan['calls']], [('goal','Inst','Probe')])

    def test_source_not_hold_is_logical_negation_in_contract(self):
        from scripts.property import emit
        source = '''relation Probe: |- int
  hint(input %0)
rule Probe/value: |- n
  -- Inst: n ~> _

property negative:
  (n : int)
  true
  -- Probe:/ |- n
'''
        plan = self.compile(source, {'schema_version':1,'observations':[
            {'id':'inst','relation':'Inst','observe':[]}]})
        self.assertEqual(plan['unsupported'], [])
        contract=emit.render_contract(plan,'Test.Contract','Test.Spec')
        self.assertIn('(¬ (SpecTec.«Probe» input.«n»))',contract)

    def test_wrapper_with_output_constraint_cannot_delegate(self):
        source = '''relation Probe: |- int
  hint(input %0)
rule Probe/value: |- n
  -- Inst: n ~> n

property probe:
  (n : int)
  Probe: |- n
'''
        plan = self.compile(source, {'schema_version':1,'observations':[
            {'id':'inst','relation':'Inst','observe':[]}]})
        self.assertEqual(plan['calls'], [])
        self.assertEqual(plan['unsupported'][0]['relation'], 'Probe')

    def test_hidden_helper_output_use_is_rejected_after_classification(self):
        source = '''relation Helper: int ~> int
  hint(input %0)
rule Helper/value: n ~> n
  -- Inst: n ~> n

property hidden:
  (n : int)
  v = v
  -- Helper: n ~> v
'''
        with self.assertRaisesRegex(ValueError, 'v.*hidden|v.*observable'):
            self.compile(source, {'schema_version':1,'observations':[
                {'id':'inst','relation':'Inst','observe':[]}]})

    def test_metadata_alone_plans_external_calls_without_execution_binding(self):
        config={'schema_version':1,'observations':[
            {'id':'value','relation':'Eval','observe':['%1.VALUE']} ]}
        plan=self.compile(config=config)
        self.assertEqual(plan['calls'][0]['relation'],'Eval')
        self.assertNotIn('adapter',plan['calls'][0])

    def test_combined_metadata_requires_migration(self):
        with self.assertRaisesRegex(ValueError,'implementation|migration|separate'):
            self.compile(config={**copy.deepcopy(CONFIG), 'executions':[{'relation':'Eval','adapter':['python3','adapter.py']}]})

    def compile(self, source=VALUE, config=None):
        try:
            from scripts.property.plan import compile_clause
        except ImportError:
            self.fail('typed external property planning is not implemented')
        return compile_clause(frontend(source), copy.deepcopy(CONFIG if config is None else config))

    def internal_config(self):
        config=copy.deepcopy(CONFIG)
        config['observations']=[x for x in config['observations'] if x['relation']!='Inst']
        return config

    def test_internal_guard_is_proof(self):
        source='property classified:\n (n : int)\n true\n -- Inst: n ~> x\n -- if $(x > n)\n'
        plan=self.compile(source,self.internal_config())
        self.assertEqual([x['origin'] for x in plan['proof_conditions']],['condition.0','condition.1'])
        self.assertEqual(len(plan['all_conditions']),2)
        self.assertEqual(plan['checks'],[])

    def test_observed_guard_is_check_and_remains_in_full_contract(self):
        source='property classified:\n (n : int)\n v = v\n -- Eval: n ~> { VALUE v, TRACE t }\n -- if $(v > n)\n'
        plan=self.compile(source)
        self.assertEqual(len(plan['all_conditions']),2)
        self.assertEqual(plan['all_conditions'][1]['expression']['operator'],'>')
        self.assertEqual([x['origin'] for x in plan['checks']],['condition.1'])
        self.assertNotIn('condition.1',[x['origin'] for x in plan['proof_conditions']])

    def test_missing_al_block_cannot_drop_source_condition(self):
        from scripts.property.plan import compile_clause
        source='property classified:\n (n : int)\n true\n -- Eval: n ~> { VALUE v, TRACE t }\n -- if $(v > n)\n'
        clause=frontend(source)
        clause['condition_blocks'].pop()
        with self.assertRaisesRegex(ValueError,'AL.*condition|condition.*AL'):
            compile_clause(clause,copy.deepcopy(CONFIG))

    def test_mixed_guard_is_rejected_after_al(self):
        source='property classified:\n (n : int)\n true\n -- Inst: n ~> x\n -- Eval: n ~> { VALUE v, TRACE t }\n -- if x = v\n'
        with self.assertRaisesRegex(ValueError,r'condition\.2.*x.*v|condition\.2.*v.*x'):
            self.compile(source,self.internal_config())

    def test_private_alias_cannot_hide_mixed_guard(self):
        source='property classified:\n (n : int)\n true\n -- Inst: n ~> x\n -- Eval: n ~> { VALUE v, TRACE t }\n -- if y = x\n -- if y = v\n'
        with self.assertRaisesRegex(ValueError,r'condition\.3.*(y|x).*(v|observ)'):
            self.compile(source,self.internal_config())

    def test_external_projection_alias_cannot_hide_mixed_guard(self):
        source='property classified:\n (n : int)\n true\n -- Inst: n ~> x\n -- Eval: n ~> r\n -- if y = r.VALUE\n -- if y = x\n'
        config=self.internal_config();config['observations'][0]['observe']=['%1']
        with self.assertRaisesRegex(ValueError,r'condition\.3.*(y|r).*(x|private|internal)'):
            self.compile(source,config)

    def test_observation_dependent_private_guard_is_rejected(self):
        source='property classified:\n (n : int)\n true\n -- Eval: n ~> { VALUE v, TRACE t }\n -- Inst: v ~> x\n -- if $(x > 0)\n'
        with self.assertRaisesRegex(ValueError,r'condition\.2.*x.*(observ|external)'):
            self.compile(source,self.internal_config())

    def test_hidden_output_runtime_guard_is_rejected(self):
        source='property classified:\n (n : int)\n true\n -- Eval: n ~> { VALUE v, TRACE t }\n -- if $(t > 0)\n'
        with self.assertRaisesRegex(ValueError,r'condition\.1.*t.*(hidden|observable)'):
            self.compile(source)

    def test_private_external_request_input_rejected(self):
        source='property classified:\n (n : int)\n true\n -- Inst: n ~> x\n -- Eval: x ~> { VALUE v, TRACE t }\n'
        with self.assertRaisesRegex(ValueError,r'condition\.1.*x.*(external|observable)'):
            self.compile(source,self.internal_config())

    def test_external_observation_can_feed_next_external_request(self):
        source='property classified:\n (n : int)\n w = w\n -- Eval: n ~> { VALUE v, TRACE t }\n -- Eval: v ~> { VALUE w, TRACE u }\n'
        plan=self.compile(source)
        self.assertEqual([x['id'] for x in plan['calls']],['condition.0','condition.1'])
        self.assertEqual(plan['calls'][1]['dependencies'],['condition.0'])

    def test_observed_alias_projection_can_feed_next_external_request(self):
        source='property classified:\n (n : int)\n true\n -- Eval: n ~> r\n -- if y = r.VALUE\n -- Eval: y ~> { VALUE w, TRACE t }\n'
        config=self.internal_config();config['observations'][0]['observe']=['%1']
        plan=self.compile(source,config)
        self.assertEqual(plan['calls'][1]['dependencies'],['condition.0'])
        self.assertEqual(plan['variables']['y']['sources'],['E'])

    def test_internal_relation_with_observed_input_is_runtime_check(self):
        source='property classified:\n (n : int)\n true\n -- Eval: n ~> { VALUE v, TRACE t }\n -- Inst: v ~> x\n'
        plan=self.compile(source,self.internal_config())
        self.assertEqual([x['id'] for x in plan['calls']],['condition.0'])
        self.assertEqual([x['origin'] for x in plan['checks']],['condition.1'])

    def test_source_goal_private_variable_rejected_but_al_local_allowed(self):
        source='property classified:\n (n : int)\n x = x\n -- Inst: n ~> x\n'
        with self.assertRaisesRegex(ValueError,r'goal.*x.*(private|internal|observable)'):
            self.compile(source,self.internal_config())
        source='property classified:\n (n : int)\n Eval: n ~> { VALUE n, TRACE t }\n'
        plan=self.compile(source)
        self.assertGreater(len(plan['goal_block']['nodes']),1)

    def test_observed_output_is_bound_and_hidden_output_remains_existential(self):
        p=self.compile()
        self.assertEqual(p['variables']['v']['producer'], 'condition.0')
        self.assertEqual(p['variables']['v']['selector'], '%1.VALUE')
        self.assertIsNone(p['variables']['t']['selector'])

    def test_hidden_output_in_goal_rejected(self):
        with self.assertRaisesRegex(ValueError,'t.*observable|observable.*t'):
            self.compile(VALUE.replace('v > n','t > n'))

    def test_progress_goal_needs_only_success(self):
        p=self.compile(PROGRESS)
        self.assertEqual([c['id'] for c in p['calls']],['condition.0','goal'])
        self.assertIsNone(p['variables']['s']['selector'])
        self.assertEqual(p['goal']['kind'],'relation')

    def test_chained_calls_use_observed_values(self):
        src='property chain:\n (n : int)\n z = v\n -- Eval: n ~> { VALUE v, TRACE t }\n -- Inst: v ~> z\n'
        config=copy.deepcopy(CONFIG);config['observations'][1]['observe']=['%1']
        p=self.compile(src,config)
        self.assertEqual(p['calls'][1]['dependencies'],['condition.0'])

    def test_unobserved_value_needed_by_later_call_rejected(self):
        with self.assertRaisesRegex(ValueError,'t.*available|available.*t|observable'):
            self.compile(PROGRESS.replace('Inst: n','Inst: t').replace('n ~> r','n ~> { VALUE v, TRACE t }'))

    def test_repeated_relation_occurrences_remain_distinct(self):
        src=VALUE+'  -- Eval: n ~> { VALUE w, TRACE u }\n'
        p=self.compile(src)
        self.assertEqual([c['id'] for c in p['calls']],['condition.0','condition.1'])

    def test_unobserved_constant_constraint_is_not_silently_dropped(self):
        with self.assertRaisesRegex(ValueError,'constraint|observable'):
            self.compile(VALUE.replace('TRACE t','TRACE 7'))

    def test_goal_relation_existing_output_constraint_is_al_guard(self):
        config=copy.deepcopy(CONFIG);config['observations'][1]['observe']=['%1']
        plan=self.compile(PROGRESS.replace('n ~> s','n ~> n'),config)
        self.assertEqual([x['kind'] for x in plan['goal_block']['nodes']],['relation','guard'])

    def test_boolean_schema_version_is_rejected(self):
        c=copy.deepcopy(CONFIG);c['schema_version']=True
        with self.assertRaisesRegex(ValueError,'schema'):
            self.compile(config=c)

    def test_missing_external_mapping_rejected(self):
        c=copy.deepcopy(CONFIG);c['observations']=[]
        with self.assertRaisesRegex(ValueError,'private|observable'):
            self.compile(config=c)

    def test_forward_dependency_rejected(self):
        src='property bad:\n (n : int)\n true\n -- Inst: v ~> z\n -- Eval: n ~> { VALUE v, TRACE t }\n'
        with self.assertRaisesRegex(ValueError,'algo/free-variable-in-expression.*v'):
            self.compile(src)

if __name__=='__main__': unittest.main()
