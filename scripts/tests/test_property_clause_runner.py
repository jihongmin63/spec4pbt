"""Subprocess collection, replay, and exact-support generator integration."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

from scripts.property.clause import build_property
from scripts.property.workflow import emit_property,check_property
from scripts.property.implementation import load_implementation
from scripts.property.runner import collect_case,recheck_trace,rerun_case,run_property
from scripts.tests.test_property_clause_build import COPY_SPEC,COPY_PROPERTY
from scripts.tests.external_selection import select_all

from scripts.tests import ROOT, FIXTURES, ORDERED, SCRATCH
CHAIN_PROPERTY='property chain:\n (n : nat)\n w = w\n -- Copy: n ~> v\n -- Copy: v ~> w\n'
INDEPENDENT_PROPERTY='property independent:\n (n : nat)\n w = w\n -- Copy: n ~> v\n -- Copy: n ~> w\n'
ADAPTER='''import json,sys,time
from pathlib import Path
r=json.load(sys.stdin)
mode=json.loads(Path(sys.argv[1]).read_text())['mode']
with open(sys.argv[2],'a') as f:f.write(r['occurrence_id']+' '+str(r['input'])+'\\n')
if mode=='timeout':time.sleep(2)
reply={key:r[key] for key in ['plan_id','case_id','occurrence_id','relation_id']}
if mode=='protocol':reply['occurrence_id']='other'
if mode=='abort':
 reply['status']='abort'
 reply['message']='target rejected execution environment'
elif mode=='reject' and r['occurrence_id']=='condition.0':
 reply['status']='relation_failure'
else:
 reply['status']='success'
 n=r['input'][0]
 value=(0 if mode=='wrong' else n+1 if mode=='advance' else n+10 if mode=='jump' else 'bad' if mode=='decode' else n)
 reply['observation']={selector:value for selector in r['observe']}
print(json.dumps(reply))
'''


class PropertyRunnerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp=tempfile.TemporaryDirectory(prefix='ClauseRunNative',dir=SCRATCH)
        cls.addClassCleanup(cls.tmp.cleanup)
        cls.root=Path(cls.tmp.name)
        cls.base='build.scratch.'+cls.root.name
        (cls.root/'spec.watsup').write_text(COPY_SPEC)
        (cls.root/'positive.watsup').write_text(COPY_PROPERTY)
        (cls.root/'chain.watsup').write_text(CHAIN_PROPERTY)
        (cls.root/'independent.watsup').write_text(INDEPENDENT_PROPERTY)
        (cls.root/'adapter.py').write_text(ADAPTER)
        (cls.root/'state.json').write_text('{"mode":"correct"}')
        command=json.dumps([sys.executable,str(cls.root/'adapter.py'),
                            str(cls.root/'state.json'),str(cls.root/'calls.log')])
        (cls.root/'config.toml').write_text(f'''schema_version = 1
[[observations]]
id = "copy"
relation = "Copy"
observe = ["%1"]
''')
        (cls.root/'implementation.toml').write_text(f'''schema_version = 1
id = "runner-test"
[[executions]]
relation = "Copy"
adapter = {command}
''')
        cls.bundles={}
        for label,template,property_name in [
            ('Positive','copy_positive_proof.lean.in','positive'),
            ('Chain','copy_chain_proof.lean.in','chain'),
            ('Independent','copy_chain_proof.lean.in','independent')]:
            module=cls.base+'.'+label+'Proof'
            proof=(ORDERED/'templates'/template).read_text()
            proof=proof.replace('@CONTRACT@',cls.base+'.'+label+'.Contract')
            (cls.root/(label+'Proof.lean')).write_text(proof)
            arguments=dict(project=ROOT,spec_paths=[cls.root/'spec.watsup'],
                property_path=cls.root/(property_name+'.watsup'),config_path=cls.root/'config.toml',
                external_path=select_all(cls.root/'config.toml'),
                name=property_name,output=cls.root/label,proof_module=module,
                property_proof=('ClauseCopy' if label=='Positive' else 'ClauseChain')+'.property_correct',
                timeout_seconds=120)
            if label=='Positive':
                emit_property(**arguments,generator_module=cls.base+'.Generator',
                              generator='ClauseCopyGenerator.generator')
                template=(ORDERED/'templates/copy_positive_generator.lean.in').read_text()
                (cls.root/'Generator.lean').write_text(template.replace('@CONTRACT@',cls.base+'.Positive.Contract')
                    .replace('@PROOF@',cls.base+'.PositiveProof'))
                cls.bundles[label]=check_property(cls.root/label)
            else:
                cls.bundles[label]=build_property(**arguments)

    def setUp(self):
        self.mode('correct')

    def mode(self,mode):
        (self.root/'state.json').write_text(json.dumps({'mode':mode}))

    def collect(self,label='Positive',n=3,timeout_seconds=1):
        return collect_case(self.bundles[label],{'n':n},self.root/self._testMethodName,
                            implementation=self.root/'implementation.toml',timeout_seconds=timeout_seconds)

    def test_observed_condition_false_fails(self):
        self.mode('wrong')
        result=self.collect()
        self.assertEqual((result.verdict,result.reason),('fail','observed_condition_false'))

    def test_external_relation_failure_is_fail(self):
        self.mode('reject')
        result=self.collect()
        self.assertEqual((result.verdict,result.reason),('fail','external_relation_failure'))

    def test_protocol_error_is_error(self):
        self.mode('protocol')
        result=self.collect()
        self.assertEqual(result.verdict,'error')
        self.assertIn('identity',result.error)

    def test_timeout_is_error(self):
        self.mode('timeout')
        result=self.collect(timeout_seconds=0.1)
        self.assertEqual(result.verdict,'error')
        self.assertIn('timeout',result.error)

    def test_explicit_adapter_abort_is_error_and_rechecks(self):
        self.mode('abort')
        result=self.collect()
        self.assertEqual((result.verdict,result.reason),('error','external_abort'))
        self.assertIn('target rejected execution environment',result.error)
        entry=json.loads(result.trace_path.read_text())['entries'][0]
        self.assertEqual(entry['status'],'abort')
        self.assertEqual(entry['raw_response']['status'],'abort')
        self.assertEqual(recheck_trace(self.bundles['Positive'],result.trace_path).verdict,'error')

    def test_decode_error_is_error(self):
        self.mode('decode')
        result=self.collect()
        self.assertEqual(result.verdict,'error')
        self.assertIn('type',result.error)

    def test_chained_request_uses_actual_output_and_blocks_on_failure(self):
        self.mode('advance')
        result=self.collect('Chain')
        entries=json.loads(result.trace_path.read_text())['entries']
        self.assertEqual([entry['input'] for entry in entries],[[3],[4]])
        self.assertEqual(result.verdict,'pass')

    def test_unavailable_dependency_is_recorded_blocked(self):
        self.mode('reject')
        result=self.collect('Chain')
        entries=json.loads(result.trace_path.read_text())['entries']
        self.assertEqual([entry['status'] for entry in entries],['relation_failure','blocked'])
        self.assertIsNone(entries[1]['input'])
        self.assertEqual(result.verdict,'fail')

    def test_independent_call_continues_after_relation_failure(self):
        self.mode('reject')
        result=self.collect('Independent')
        entries=json.loads(result.trace_path.read_text())['entries']
        self.assertEqual([entry['status'] for entry in entries],['relation_failure','success'])
        self.assertEqual(entries[1]['input'],[3])

    def test_recheck_uses_saved_response_and_rejects_tampering(self):
        result=self.collect()
        before=(self.root/'calls.log').read_text()
        self.assertEqual(recheck_trace(self.bundles['Positive'],result.trace_path).verdict,'pass')
        self.assertEqual((self.root/'calls.log').read_text(),before)
        record=json.loads(result.trace_path.read_text())
        record['entries'][0]['occurrence_id']='goal'
        result.trace_path.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError,'occurrence identity'):
            recheck_trace(self.bundles['Positive'],result.trace_path)

    def test_version_one_trace_is_not_reused(self):
        result=self.collect()
        record=json.loads(result.trace_path.read_text());record['schema_version']=2
        result.trace_path.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError,'schema 3'):
            recheck_trace(self.bundles['Positive'],result.trace_path)

    def test_saved_response_and_certificate_tampering_are_rejected(self):
        result=self.collect()
        original=json.loads(result.trace_path.read_text())
        for change,pattern in [
            (lambda record:record.update(certificate_sha256='wrong'),'certificate'),
            (lambda record:record['entries'][0]['raw_response'].update(occurrence_id='other'),'raw response'),
            (lambda record:record['entries'][0]['raw_response'].update(unexpected='field'),'response fields'),
            (lambda record:record['entries'][0].update(error='forged'),'trace error'),
            (lambda record:record['entries'][0].update(status='abort',observation={}),'abort status'),
            (lambda record:record['entries'][0].update(input=[99]),'request input')]:
            record=json.loads(json.dumps(original));change(record)
            result.trace_path.write_text(json.dumps(record))
            with self.assertRaisesRegex(ValueError,pattern):
                recheck_trace(self.bundles['Positive'],result.trace_path)

    def test_stale_proof_and_native_binary_are_rejected(self):
        bundle=self.bundles['Positive']
        paths=[self.root/'PositiveProof.lean',bundle.executable]
        for path in paths:
            original=path.read_bytes()
            try:
                path.write_bytes(original+b'\n')
                with self.assertRaisesRegex(ValueError,'stale'):
                    bundle.request({'n':3},[],0)
            finally:
                path.write_bytes(original)

    def test_rerun_recomputes_dependent_requests(self):
        self.mode('advance')
        first=self.collect('Chain')
        self.mode('jump')
        rerun=rerun_case(self.bundles['Chain'],first.case_dir,self.root/('rerun-'+self._testMethodName),
                         implementation=self.root/'implementation.toml')
        entries=json.loads(rerun.trace_path.read_text())['entries']
        self.assertEqual([entry['input'] for entry in entries],[[3],[13]])

    def test_rerun_selects_different_implementation_and_new_chain(self):
        self.mode('advance')
        first=self.collect('Chain')
        (self.root/'adapter2.py').write_text(ADAPTER)
        (self.root/'state2.json').write_text('{"mode":"jump"}')
        command=json.dumps([sys.executable,str(self.root/'adapter2.py'),
                            str(self.root/'state2.json'),str(self.root/'calls2.log')])
        second_manifest=self.root/'implementation2.toml'
        second_manifest.write_text('schema_version = 1\nid = "second"\n[[executions]]\nrelation = "Copy"\nadapter = '+command+'\n')
        second=rerun_case(self.bundles['Chain'],first.case_dir,
                          self.root/('rerun-'+self._testMethodName),implementation=second_manifest)
        old=json.loads(first.trace_path.read_text())
        new=json.loads(second.trace_path.read_text())
        self.assertEqual([e['input'] for e in old['entries']],[[3],[4]])
        self.assertEqual([e['input'] for e in new['entries']],[[3],[13]])
        self.assertNotEqual(old['implementation']['identity'],new['implementation']['identity'])
        self.assertEqual(old['plan_id'],new['plan_id'])

    def test_offline_recheck_and_saved_binding_tamper(self):
        artifact=self.root/'offline-target.bin'
        artifact.write_bytes(b'target-v1')
        manifest=self.root/'offline-implementation.toml'
        manifest.write_text((self.root/'implementation.toml').read_text()+
                            'artifacts = ["offline-target.bin"]\n')
        result=collect_case(self.bundles['Positive'],{'n':3},self.root/self._testMethodName,
                            implementation=manifest)
        adapter=self.root/'adapter.py'
        source=adapter.read_bytes()
        try:
            adapter.unlink()
            manifest.unlink()
            artifact.unlink()
            self.assertEqual(recheck_trace(self.bundles['Positive'],result.trace_path).verdict,'pass')
        finally:
            adapter.write_bytes(source)
        trace=json.loads(result.trace_path.read_text())
        trace['entries'][0]['binding_id']='tampered'
        result.trace_path.write_text(json.dumps(trace))
        with self.assertRaisesRegex(ValueError,'binding identity'):
            recheck_trace(self.bundles['Positive'],result.trace_path)

    def test_adapter_change_stales_only_implementation(self):
        binding=load_implementation(self.root/'implementation.toml',self.bundles['Positive'])
        adapter=self.root/'adapter.py'
        original=adapter.read_bytes()
        try:
            adapter.write_bytes(original+b'\n')
            self.bundles['Positive'].assert_fresh()
            with self.assertRaisesRegex(ValueError,'implementation is stale'):
                collect_case(self.bundles['Positive'],{'n':3},self.root/self._testMethodName,
                             implementation=binding)
            self.assertFalse((self.root/self._testMethodName).exists())
        finally:
            adapter.write_bytes(original)

    def test_outcome_criteria_are_required_as_a_complete_set_and_frozen(self):
        manifest=self.root/'classified-implementation.toml'
        manifest.write_text((self.root/'implementation.toml').read_text().replace(
            'schema_version = 1','schema_version = 2',1)+'''\n[executions.outcomes]
match = "target accepts the relation input"
unmatch = "target rejects a valid request normally"
abort = "target cannot evaluate the request"
''')
        binding=load_implementation(manifest,self.bundles['Positive'])
        self.assertEqual(set(binding.snapshot['bindings']['Copy']['outcomes']),
                         {'match','unmatch','abort'})
        self.mode('abort')
        result=collect_case(self.bundles['Positive'],{'n':3},self.root/self._testMethodName,
                            implementation=manifest)
        self.assertEqual((result.verdict,result.reason),('error','external_abort'))
        record=json.loads(result.trace_path.read_text())
        record['implementation']['bindings']['Copy']['outcomes']['abort']='changed'
        result.trace_path.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError,'binding identity'):
            recheck_trace(self.bundles['Positive'],result.trace_path)
        incomplete=self.root/'incomplete-implementation.toml'
        incomplete.write_text(manifest.read_text().replace('abort = "target cannot evaluate the request"\n',''))
        with self.assertRaisesRegex(ValueError,'outcomes'):
            load_implementation(incomplete,self.bundles['Positive'])
        omitted=self.root/'unclassified-implementation.toml'
        omitted.write_text((self.root/'implementation.toml').read_text().replace(
            'schema_version = 1','schema_version = 2',1))
        with self.assertRaisesRegex(ValueError,'outcomes'):
            load_implementation(omitted,self.bundles['Positive'])

    def test_artifact_change_during_adapter_call_is_rejected(self):
        artifact=self.root/'changing-target.bin'
        artifact.write_bytes(b'v1')
        script=self.root/'mutating-adapter.py'
        script.write_text('''import json,sys
from pathlib import Path
r=json.load(sys.stdin)
Path(sys.argv[1]).write_bytes(b'v2')
reply={key:r[key] for key in ('plan_id','case_id','occurrence_id','relation_id')}
reply.update(status='success',observation={s:r['input'][0] for s in r['observe']})
print(json.dumps(reply))
''')
        manifest=self.root/'mutating-implementation.toml'
        command=json.dumps([sys.executable,str(script),str(artifact)])
        manifest.write_text('schema_version = 1\nid = "mutating"\n[[executions]]\n'
                            'relation = "Copy"\nadapter = '+command+'\n'
                            'artifacts = ["changing-target.bin"]\n')
        with self.assertRaisesRegex(ValueError,'implementation is stale'):
            collect_case(self.bundles['Positive'],{'n':3},self.root/self._testMethodName,
                         implementation=manifest)

    def test_certified_generator_run_never_samples_zero(self):
        result=run_property(self.bundles['Positive'],generator_module=self.base+'.Generator',
            generator='ClauseCopyGenerator.generator',output=self.root/self._testMethodName,
            implementation=self.root/'implementation.toml',count=3,size=8,seed=0,timeout_seconds=120)
        self.assertEqual((result.status,result.counts['pass']),('passed',3))
        samples=json.loads((result.output/'samples.json').read_text())
        self.assertTrue(all(sample['input']['n']>0 for sample in samples))

    def test_preflight_missing_binding_prevents_sampling_and_target(self):
        missing=self.root/'missing-binding.toml'
        missing.write_text('schema_version = 1\nid = "empty"\nexecutions = []\n')
        log=self.root/'calls.log'
        before=log.read_text() if log.exists() else ''
        with self.assertRaisesRegex(ValueError,'missing.*Copy'):
            run_property(self.bundles['Positive'],generator_module=self.base+'.Generator',
                generator='ClauseCopyGenerator.generator',output=self.root/self._testMethodName,
                implementation=missing,count=1)
        self.assertFalse((self.root/self._testMethodName).exists())
        self.assertEqual(log.read_text() if log.exists() else '',before)


if __name__=='__main__':unittest.main()
