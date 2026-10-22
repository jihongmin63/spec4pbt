"""The official AL interpreter consumes frozen external observations."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from translator.toolchain import resolve_toolchain, PROPERTY_EXECUTABLE, PROPERTY_RUN_EXECUTABLE
from pbt.property.plan import compile_clause
from tests.test_property_clause import frontend

from tests import ROOT, FIXTURES, ORDERED, SCRATCH
SPEC='''var n : nat
relation Parse: nat ~> nat
  hint(input %0)
rule Parse/value: n ~> n
relation Run: nat ~> nat
  hint(input %0)
rule Run/value: n ~> n
'''
CONFIG={'schema_version':1,
        'observations':[{'id':'parse','relation':'Parse','observe':['%1']},
                        {'id':'run','relation':'Run','observe':['%1']}]}


class NativePropertyExecutorTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(prefix='PropertyExec',dir=SCRATCH)
        self.addCleanup(self.tmp.cleanup)
        self.folder=Path(self.tmp.name)
        (self.folder/'spec.watsup').write_text(SPEC)
        self.exe=resolve_toolchain(ROOT).root/PROPERTY_RUN_EXECUTABLE

    def load(self,source,*,spec=SPEC,config=CONFIG):
        (self.folder/'spec.watsup').write_text(spec)
        (self.folder/'property.watsup').write_text(source)
        plan=compile_clause(frontend(source,spec),config)
        (self.folder/'plan.json').write_text(json.dumps(plan))
        return plan

    def invoke(self,plan,mode,input_value,trace,index=None):
        payload={'plan_id':plan['plan_id'],'mode':mode,'input':input_value,'trace':trace}
        if index is not None:payload['index']=index
        result=subprocess.run([str(self.exe),'--spec',str(self.folder/'spec.watsup'),
            '--property',str(self.folder/'property.watsup'),'--name',plan['name'],
            '--plan',str(self.folder/'plan.json')],input=json.dumps(payload),text=True,
            capture_output=True,timeout=20)
        if result.returncode:raise ValueError(result.stderr)
        return json.loads(result.stdout)

    def test_parse_observation_flows_into_run_request(self):
        plan=self.load('property chain:\n (n : nat)\n w = w\n -- Parse: n ~> v\n -- Run: v ~> w\n')
        first={'occurrence_id':'condition.0','relation_id':'Parse','input':[3],
               'status':'success','observation':{'%1':4}}
        self.assertEqual(self.invoke(plan,'request',{'n':3},[],0),{'ready':True,'input':[3]})
        self.assertEqual(self.invoke(plan,'request',{'n':3},[first],1),{'ready':True,'input':[4]})
        second={'occurrence_id':'condition.1','relation_id':'Run','input':[4],
                'status':'success','observation':{'%1':9}}
        self.assertEqual(self.invoke(plan,'check',{'n':3},[first,second])['verdict'],'pass')
        blocked={**first,'status':'relation_failure','observation':{}}
        self.assertEqual(self.invoke(plan,'request',{'n':3},[blocked],1),{'ready':False})
        with self.assertRaisesRegex(ValueError,'request input mismatch'):
            self.invoke(plan,'check',{'n':3},[first,{**second,'input':[3]}])

    def test_observed_guard_does_not_suppress_independent_call(self):
        source='property independent:\n (n : nat)\n w = w\n -- Parse: n ~> v\n -- if $(v > 0)\n -- Run: n ~> w\n'
        plan=self.load(source)
        first={'occurrence_id':'condition.0','relation_id':'Parse','input':[3],
               'status':'success','observation':{'%1':0}}
        self.assertEqual(self.invoke(plan,'request',{'n':3},[first],1),
                         {'ready':True,'input':[3]})
        second={'occurrence_id':'condition.2','relation_id':'Run','input':[3],
                'status':'success','observation':{'%1':3}}
        self.assertEqual(self.invoke(plan,'check',{'n':3},[first,second])['reason'],
                         'observed_condition_false')

    def test_goal_output_match_guard_uses_observed_value(self):
        plan=self.load('property goal_match:\n (n : nat)\n Run: n ~> n\n')
        self.assertEqual([node['kind'] for node in plan['goal_block']['nodes']],['relation','guard'])
        good=[{'occurrence_id':'goal','relation_id':'Run','input':[3],
               'status':'success','observation':{'%1':3}}]
        self.assertEqual(self.invoke(plan,'check',{'n':3},good)['verdict'],'pass')
        bad=[{**good[0],'observation':{'%1':0}}]
        self.assertEqual(self.invoke(plan,'check',{'n':3},bad)['reason'],'goal_false')

    def test_goal_index_guard_fails_after_collection(self):
        plan=self.load('property indexed:\n (xs : nat*) (i : nat)\n xs[i] = xs[i]\n')
        self.assertEqual(plan['calls'],[])
        self.assertGreater(len(plan['goal_block']['nodes']),1)
        self.assertEqual(self.invoke(plan,'check',{'xs':[3,4],'i':1},[])['verdict'],'pass')
        self.assertEqual(self.invoke(plan,'check',{'xs':[3,4],'i':2},[])['reason'],'goal_false')

    def test_partial_record_observation_is_typed_without_hidden_defaults(self):
        from tests.test_property_frontend import SPEC as RECORD_SPEC
        config={'schema_version':1,
                'observations':[{'id':'eval','relation':'Eval','observe':['%1.VALUE']}]}
        plan=self.load('property record:\n (n : int)\n true\n -- Eval: n ~> r\n',
                       spec=RECORD_SPEC,config=config)
        self.assertIsNone(plan['variables']['r']['selector'])
        good=[{'occurrence_id':'condition.0','relation_id':'Eval','input':[3],
               'status':'success','observation':{'%1.VALUE':4}}]
        self.assertEqual(self.invoke(plan,'check',{'n':3},good)['verdict'],'pass')
        with self.assertRaisesRegex(ValueError,'observation type mismatch'):
            self.invoke(plan,'check',{'n':3},[{**good[0],'observation':{'%1.VALUE':'bad'}}])

    def test_hidden_external_effect_in_internal_goal_is_rejected_by_audit(self):
        spec='''var n : nat
var x : nat
extern relation External: nat ~> nat
  hint(input %0)
relation Wrapper: nat ~> nat
  hint(input %0)
rule Wrapper/value:
  n ~> x
  -- External: n ~> x
'''
        source='property hidden:\n (n : nat)\n Wrapper: n ~> x\n'
        plan=self.load(source,spec=spec,config={'schema_version':1})
        with self.assertRaisesRegex(ValueError,'dynamic external call'):
            self.invoke(plan,'audit',{'n':3},[])

    def test_hidden_external_effect_in_internal_condition_is_rejected_by_audit(self):
        spec='''var n : nat
var x : nat
extern relation External: nat ~> nat
  hint(input %0)
relation Wrapper: nat ~> nat
  hint(input %0)
rule Wrapper/value:
  n ~> x
  -- External: n ~> x
'''
        source='property hidden_condition:\n (n : nat)\n true\n -- Wrapper: n ~> x\n'
        plan=self.load(source,spec=spec,config={'schema_version':1})
        with self.assertRaisesRegex(ValueError,'dynamic external call'):
            self.invoke(plan,'audit',{'n':3},[])

    def test_hidden_function_call_in_internal_output_is_rejected_by_audit(self):
        spec='''var n : nat
extern dec $opaque(nat) : nat
relation Wrapper: nat ~> nat
  hint(input %0)
rule Wrapper/value: n ~> $opaque(n)
'''
        source='property hidden_output:\n (n : nat)\n true\n -- Wrapper: n ~> x\n'
        plan=self.load(source,spec=spec,config={'schema_version':1})
        with self.assertRaisesRegex(ValueError,'dynamic function call'):
            self.invoke(plan,'audit',{'n':3},[])


if __name__=='__main__':unittest.main()
