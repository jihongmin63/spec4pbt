"""Runnable ordered property examples with certified generators."""
import json
from pathlib import Path
import tempfile
import unittest

from pbt.property.runner import collect_case,run_property
from examples.ordered.run import build_example
from pbt.property.clause import build_property,load_clause
from pbt.property.plan import compile_clause

ROOT=Path(__file__).resolve().parents[2]


class PropertyExamplesTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp=tempfile.TemporaryDirectory(prefix='ClauseDemoOrdered',dir=ROOT/'pbt')
        cls.addClassCleanup(cls.tmp.cleanup)
        cls.root=Path(cls.tmp.name)
        cls.cache={}

    def example(self,name,mode='correct'):
        key=name
        if key not in self.cache:
            self.cache[key]=build_example(name,self.root/('Bundle'+str(len(self.cache))))
        return self.cache[key]

    def run_example(self,name,mode='correct'):
        bundle,module,generator=self.example(name,mode)
        result=run_property(bundle,generator_module=module,generator=generator,
            implementation=ROOT/'examples/ordered'/('implementations/'+mode+'.toml'),
            output=self.root/(self._testMethodName+'-'+name+'-'+mode),count=2,size=6,seed=0)
        return result

    def test_same_certified_bundle_runs_distinct_implementations(self):
        bundle,_,_=self.example('positive')
        good=self.run_example('positive','correct')
        bad=self.run_example('positive','zero')
        good_trace=json.loads((good.output/'case-000000/trace.json').read_text())
        bad_trace=json.loads((bad.output/'case-000000/trace.json').read_text())
        self.assertEqual(good_trace['plan_id'],bad_trace['plan_id'])
        self.assertEqual(good_trace['certificate_sha256'],bad_trace['certificate_sha256'])
        self.assertNotEqual(good_trace['implementation']['identity'],bad_trace['implementation']['identity'])
        self.assertEqual((good.status,bad.status),('passed','failed'))
        self.assertEqual(json.loads((bad.output/'case-000000/result.json').read_text())['reason'],
                         'observed_condition_false')

    def test_observed_guard_generator_excludes_zero(self):
        result=self.run_example('positive')
        self.assertEqual((result.status,result.counts['pass']),('passed',2))
        samples=json.loads((result.output/'samples.json').read_text())
        self.assertTrue(all(sample['input']['n']>0 for sample in samples))

    def test_wrong_observation_fails_even_with_tautological_goal(self):
        result=self.run_example('positive','zero')
        self.assertEqual((result.status,result.counts['fail']),('failed',2))
        case=json.loads((result.output/'case-000000/result.json').read_text())
        self.assertEqual(case['reason'],'observed_condition_false')

    def test_internal_private_witness_uses_same_positive_generator_contract(self):
        result=self.run_example('internal_positive')
        self.assertEqual(result.status,'passed')
        trace=json.loads((result.output/'case-000000/trace.json').read_text())
        self.assertEqual(trace['entries'],[])
        samples=json.loads((result.output/'samples.json').read_text())
        self.assertTrue(all(sample['input']['n']>0 for sample in samples))

    def test_progress_external_goal_rejection_is_fail(self):
        passed=self.run_example('progress')
        self.assertEqual(passed.status,'passed')
        failed=self.run_example('progress','reject')
        self.assertEqual((failed.status,failed.counts['fail']),('failed',2))

    def test_chained_output_is_forwarded_to_second_request(self):
        result=self.run_example('chain')
        self.assertEqual(result.status,'passed')
        trace=json.loads((result.output/'case-000000/trace.json').read_text())
        first,second=trace['entries']
        self.assertEqual(second['input'],[first['observation']['%1']])

    def test_empty_observation_relation_collects_status(self):
        root=ROOT/'examples/ordered'
        config=self.root/'status-observations.toml'
        config.write_text('schema_version = 1\n[[observations]]\nid = "copy-status"\nrelation = "Copy"\nobserve = []\n')
        output=self.root/'StatusBundle'
        proof_module='pbt.'+self.root.name+'.StatusBundleProof'
        template=(ROOT/'examples/ordered/templates/progress_proof.lean.in').read_text()
        (self.root/'StatusBundleProof.lean').write_text(template.replace('@CONTRACT@',
            'pbt.'+self.root.name+'.StatusBundle.Contract'))
        bundle=build_property(spec_paths=[root/'spec.watsup'],
            property_path=root/'properties.watsup',config_path=config,
            name='progress',output=output,proof_module=proof_module,
            property_proof='ClauseProgress.property_correct')
        good=collect_case(bundle,{'n':3},self.root/'status-good',
            implementation=root/'implementations/correct.toml')
        bad=collect_case(bundle,{'n':3},self.root/'status-bad',
            implementation=root/'implementations/reject.toml')
        self.assertEqual((good.verdict,bad.verdict),('pass','fail'))
        self.assertEqual(json.loads(good.trace_path.read_text())['entries'][0]['observation'],{})

    def test_mixed_private_and_observed_condition_is_rejected(self):
        root=ROOT/'examples/ordered'
        clause=load_clause([root/'spec.watsup'],root/'properties.watsup','mixed')
        import tomllib
        with (root/'observations.toml').open('rb') as f:config=tomllib.load(f)
        with self.assertRaisesRegex(ValueError,'mixed private and observable'):
            compile_clause(clause,config)

    def test_sorry_generator_rejected_before_adapter_execution(self):
        bundle,_,_=self.example('positive')
        file=bundle.directory/'BadGenerator.lean'
        file.write_text(f'import {bundle.module}\nimport pbt.CorrectGen\ndef bad : CorrectGen {bundle.namespace}.Premise := by sorry\n')
        with self.assertRaisesRegex(ChildProcessError,'sorry|axiom|forbidden'):
            run_property(bundle,generator_module=bundle.module.rsplit('.',1)[0]+'.BadGenerator',
                generator='bad',output=self.root/self._testMethodName,count=1,
                implementation=ROOT/'examples/ordered/implementations/correct.toml')

    def test_zero_count_rejected(self):
        bundle,module,generator=self.example('positive')
        with self.assertRaisesRegex(ValueError,'count'):
            run_property(bundle,generator_module=module,generator=generator,
                output=self.root/self._testMethodName,count=0,
                implementation=ROOT/'examples/ordered/implementations/correct.toml')


if __name__=='__main__':unittest.main()
