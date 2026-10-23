"""Runnable ordered property examples with certified generators."""
import json
from pathlib import Path
import tempfile
import unittest

from pbt.property.runner import collect_case,run_property
from tests.ordered.run import build_example
from tests.external_selection import select_all
from pbt.property.clause import build_property,load_clause
from pbt.property.workflow import emit_property,check_property
from pbt.property.plan import compile_clause

from tests import ROOT, FIXTURES, ORDERED, SCRATCH


class PropertyExamplesTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp=tempfile.TemporaryDirectory(prefix='ClauseDemoOrdered',dir=SCRATCH)
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
            implementation=ORDERED/('implementations/'+mode+'.toml'),
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

    def test_certified_progress_with_unused_external_type_needs_no_model(self):
        folder = self.root / 'SingletonProgress'
        folder.mkdir()
        base = '.'.join(folder.relative_to(ROOT).parts)
        contract = base + '.Bundle.Contract'
        spec = folder / 'spec.watsup'
        spec.write_text('extern syntax archState\n' + (ORDERED / 'spec.watsup').read_text())
        proof = (ORDERED / 'templates/progress_proof.lean.in').read_text()
        (folder / 'Proof.lean').write_text(proof.replace('@CONTRACT@', contract))
        emit_property(spec_paths=[spec],
            property_path=ORDERED / 'properties.watsup', config_path=ORDERED / 'observations.toml',
            external_path=ORDERED / 'external/progress.toml',
            name='progress', output=folder / 'Bundle', proof_module=base + '.Proof',
            property_proof='ClauseProgress.property_correct',
            generator_module=base+'.Generator',generator='ClauseProgressGenerator.generator')
        generator = (ORDERED / 'templates/progress_generator.lean.in').read_text()
        (folder / 'Generator.lean').write_text(generator.replace('@CONTRACT@', contract)
            .replace('@PROOF@', base + '.Proof'))
        bundle = check_property(folder / 'Bundle')
        result = run_property(bundle, generator_module=base + '.Generator',
            generator='ClauseProgressGenerator.generator',
            implementation=ORDERED / 'implementations/correct.toml',
            output=folder / 'results', count=2, size=6, seed=0)
        self.assertEqual((result.status, result.counts['pass']), ('passed', 2))

    def test_chained_output_is_forwarded_to_second_request(self):
        result=self.run_example('chain')
        self.assertEqual(result.status,'passed')
        trace=json.loads((result.output/'case-000000/trace.json').read_text())
        first,second=trace['entries']
        self.assertEqual(second['input'],[first['observation']['%1']])

    def test_empty_observation_relation_collects_status(self):
        root=ORDERED
        config=self.root/'status-observations.toml'
        config.write_text('schema_version = 1\n[[observations]]\nid = "copy-status"\nrelation = "Copy"\nobserve = []\n')
        output=self.root/'StatusBundle'
        proof_module='out.scratch.'+self.root.name+'.StatusBundleProof'
        template=(ORDERED/'templates/progress_proof.lean.in').read_text()
        (self.root/'StatusBundleProof.lean').write_text(template.replace('@CONTRACT@',
            'out.scratch.'+self.root.name+'.StatusBundle.Contract'))
        bundle=build_property(spec_paths=[root/'spec.watsup'],
            property_path=root/'properties.watsup',config_path=config,
            external_path=select_all(config),
            name='progress',output=output,proof_module=proof_module,
            property_proof='ClauseProgress.property_correct')
        good=collect_case(bundle,{'n':3},self.root/'status-good',
            implementation=root/'implementations/correct.toml')
        bad=collect_case(bundle,{'n':3},self.root/'status-bad',
            implementation=root/'implementations/reject.toml')
        self.assertEqual((good.verdict,bad.verdict),('pass','fail'))
        self.assertEqual(json.loads(good.trace_path.read_text())['entries'][0]['observation'],{})

    def test_mixed_private_and_observed_condition_is_rejected(self):
        root=ORDERED
        clause=load_clause([root/'spec.watsup'],root/'properties.watsup','mixed')
        import tomllib
        with (root/'observations.toml').open('rb') as f:config=tomllib.load(f)
        with self.assertRaisesRegex(ValueError,'mixed private and observable'):
            compile_clause(clause,config)

    def test_sorry_generator_rejected_before_adapter_execution(self):
        bundle,_,_=build_example('positive',self.root/'SorryGenerator')
        file=bundle.directory/'Generator.lean'
        file.write_text(f'import {bundle.module}\nimport Spec4Pbt.CorrectGen\n'
                        f'def ClauseCopyGenerator.generator : CorrectGen {bundle.namespace}.Premise := by sorry\n')
        with self.assertRaisesRegex(ChildProcessError,'sorry|axiom|forbidden'):
            check_property(bundle.directory)
        self.assertFalse((bundle.directory/'certificate.json').exists())

    def test_zero_count_rejected(self):
        bundle,module,generator=self.example('positive')
        with self.assertRaisesRegex(ValueError,'count'):
            run_property(bundle,generator_module=module,generator=generator,
                output=self.root/self._testMethodName,count=0,
                implementation=ORDERED/'implementations/correct.toml')


if __name__=='__main__':unittest.main()
