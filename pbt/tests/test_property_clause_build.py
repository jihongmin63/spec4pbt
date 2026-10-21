"""Compile clauses and check actual observations using the generated Lean driver."""
import json
from pathlib import Path
import tempfile
import unittest
import subprocess
from translator.toolchain import resolve_toolchain
from translator.tests.test_property_clause import SPEC, VALUE, PROGRESS
from pbt.tests.test_property_clause import frontend

ROOT=Path(__file__).resolve().parents[2]
CONFIG='''schema_version = 1
[[observations]]
id = "value"
relation = "Eval"
observe = ["%1.VALUE"]
[[observations]]
id = "inst"
relation = "Inst"
observe = []
'''

COPY_SPEC='''var n : nat
relation Copy: nat ~> nat
  hint(input %0)
rule Copy/value: n ~> n
'''
COPY_PROPERTY='''property positive:
 (n : nat)
 v = v
 -- Copy: n ~> v
 -- if $(v > 0)
'''
COPY_CONFIG={'schema_version':1,'observations':[{'id':'copy','relation':'Copy','observe':['%1']}],
}


class PropertyContractTests(unittest.TestCase):
    def test_sorry_property_proof_is_rejected(self):
        from pbt.property.clause import build_property
        with tempfile.TemporaryDirectory(prefix='ClauseBadProof',dir=ROOT/'pbt') as tmp:
            folder=Path(tmp);base='pbt.'+folder.name;output=folder/'Bundle'
            (folder/'spec.watsup').write_text(COPY_SPEC)
            (folder/'property.watsup').write_text(COPY_PROPERTY)
            (folder/'config.toml').write_text('''schema_version = 1
[[observations]]
id = "copy"
relation = "Copy"
observe = ["%1"]
''')
            contract=base+'.Bundle.Contract'
            (folder/'Proof.lean').write_text(f'''import {contract}
namespace BadProof
theorem property_correct : {contract}.SpecProperty := by sorry
end BadProof
''')
            with self.assertRaisesRegex((ValueError,ChildProcessError),'sorry|forbidden|axiom'):
                build_property(project=ROOT,spec_paths=[folder/'spec.watsup'],
                    property_path=folder/'property.watsup',config_path=folder/'config.toml',
                    name='positive',output=output,proof_module=base+'.Proof',
                    property_proof='BadProof.property_correct',timeout_seconds=90)
            self.assertFalse(output.exists())

    def test_property_proof_and_actual_observed_guard_failure(self):
        from pbt.property.clause import build_property, load_bundle
        with tempfile.TemporaryDirectory(prefix='ClausePositiveNative',dir=ROOT/'pbt') as tmp:
            folder=Path(tmp);base='pbt.'+folder.name;output=folder/'Bundle'
            (folder/'spec.watsup').write_text(COPY_SPEC)
            (folder/'property.watsup').write_text(COPY_PROPERTY)
            (folder/'config.toml').write_text('''schema_version = 1
[[observations]]
id = "copy"
relation = "Copy"
observe = ["%1"]
''')
            proof=(ROOT/'examples/ordered/templates/copy_positive_proof.lean.in').read_text()
            (folder/'Proof.lean').write_text(proof.replace('@CONTRACT@',base+'.Bundle.Contract'))
            bundle=build_property(project=ROOT,spec_paths=[folder/'spec.watsup'],
                property_path=folder/'property.watsup',config_path=folder/'config.toml',
                name='positive',output=output,proof_module=base+'.Proof',
                property_proof='ClauseCopy.property_correct',timeout_seconds=120)
            self.assertEqual(bundle.plan['relation_semantics'],'ordered')
            self.assertEqual(bundle.request({'n':3},[],0),{'ready':True,'input':[3]})
            good=[{'occurrence_id':'condition.0','relation_id':'Copy','input':[3],
                   'status':'success','observation':{'%1':3}}]
            self.assertEqual(load_bundle(output).evaluate({'n':3},good),'pass')
            bad=[{**good[0],'observation':{'%1':0}}]
            self.assertEqual(bundle.invoke('check',{'n':3},bad)['reason'],'observed_condition_false')
            generator=(ROOT/'examples/ordered/templates/copy_positive_generator.lean.in').read_text()
            (folder/'Generator.lean').write_text(generator.replace('@CONTRACT@',base+'.Bundle.Contract')
                .replace('@PROOF@',base+'.Proof'))
            from pbt.property.runner import sample_inputs
            samples,_=sample_inputs(bundle,base+'.Generator','ClauseCopyGenerator.generator',
                count=8,size=8,seed=0,timeout_seconds=120)
            self.assertTrue(all(item['input']['n']>0 for item in samples))
            with self.assertRaisesRegex(ValueError,'occurrence identity'):
                bundle.evaluate({'n':3},[{**good[0],'occurrence_id':'goal'}])
            (folder/'Proof.lean').write_text((folder/'Proof.lean').read_text()+'\n-- stale\n')
            with self.assertRaisesRegex(ValueError,'stale'):
                bundle.evaluate({'n':3},good)

    def test_build_requires_property_proof(self):
        from pbt.property.clause import build_property
        with tempfile.TemporaryDirectory(prefix='ClauseMissingProof',dir=ROOT/'pbt') as tmp:
            folder=Path(tmp)
            (folder/'spec.watsup').write_text(COPY_SPEC)
            (folder/'property.watsup').write_text(COPY_PROPERTY)
            (folder/'config.toml').write_text('''schema_version = 1
[[observations]]
id = "copy"
relation = "Copy"
observe = ["%1"]
''')
            with self.assertRaisesRegex(ValueError,'proof_module|property_proof'):
                build_property(project=ROOT,spec_paths=[folder/'spec.watsup'],
                    property_path=folder/'property.watsup',config_path=folder/'config.toml',
                    name='positive',output=folder/'Bundle',timeout_seconds=90)

    def _prove_positive_premise(self,spec,source,config,relation):
        from pbt.property.plan import compile_clause
        from pbt.property import emit as property_emit
        plan=compile_clause(frontend(source,spec),config)
        with tempfile.TemporaryDirectory(prefix='ClauseContract',dir=ROOT/'pbt') as tmp:
            folder=Path(tmp)
            base='pbt.'+folder.name
            spec_file=folder/'source.watsup';spec_file.write_text(spec)
            tool=resolve_toolchain(ROOT)
            translated=subprocess.run([str(tool.executable),'--relation-semantics','ordered',str(spec_file)],
                                      capture_output=True,text=True,check=True)
            (folder/'Spec.lean').write_text(translated.stdout)
            (folder/'Contract.lean').write_text(property_emit.render_contract(plan,base+'.Contract',base+'.Spec'))
            proof=f'''import {base}.Contract

namespace ContractCheck
theorem copy_refl (n : Nat) : SpecTec.{relation} n n := by
  refine ⟨0, ?_⟩
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.{relation}_clauses n) ()) 0
    (.success (.of n)) 0
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram (.pure n) 0
    (.success (.of n)) 0
  exact SpecTecExecution.Eval.pure n

theorem copy_eq (n v : Nat) (h : SpecTec.{relation} n v) : v = n := by
  rcases h with ⟨final, h⟩
  rcases copy_refl n with ⟨_, href⟩
  have det : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
    intro request x y hx
    cases hx
  have heq := (SpecTecExecution.eval_deterministic det h href).1
  cases heq
  rfl

theorem premise_positive (n : Nat) :
    {base}.Contract.Premise ⟨n⟩ ↔ n > 0 := by
  change (∃ v : Nat, SpecTec.{relation} n v ∧ decide (v > 0) = true) ↔ n > 0
  constructor
  · rintro ⟨v, hc, hg⟩
    have hv := copy_eq n v hc
    subst v
    simpa using hg
  · intro hn
    exact ⟨n, copy_refl n, decide_eq_true hn⟩
end ContractCheck
'''
            (folder/'Proof.lean').write_text(proof)
            build=subprocess.run(['lake','build',base+'.Spec',base+'.Contract'],cwd=ROOT,
                                 capture_output=True,text=True,timeout=120)
            self.assertEqual(build.returncode,0,build.stdout+build.stderr)
            checked=subprocess.run(['lake','env','lean',str(folder/'Proof.lean')],cwd=ROOT,
                                   capture_output=True,text=True,timeout=120)
            self.assertEqual(checked.returncode,0,checked.stdout+checked.stderr)

    def test_ordered_copy_premise_is_positive_input_in_lean(self):
        self._prove_positive_premise(COPY_SPEC,COPY_PROPERTY,COPY_CONFIG,'Copy')

    def test_internal_output_condition_shares_lean_witness(self):
        spec=COPY_SPEC.replace('Copy','Internal')
        source=COPY_PROPERTY.replace('Copy','Internal').replace('v = v','true')
        self._prove_positive_premise(spec,source,{'schema_version':1},'Internal')

    def test_observed_guard_is_in_full_premise(self):
        from pbt.property.plan import compile_clause
        from pbt.property import emit as property_emit
        plan=compile_clause(frontend(COPY_PROPERTY,COPY_SPEC),COPY_CONFIG)
        self.assertEqual(len(plan['all_conditions']),2)
        self.assertEqual([x['origin'] for x in plan['checks']],['condition.1'])
        source=property_emit.render_contract(plan,'ClauseContract','ClauseSpec')
        self.assertIn('def Premise',source)
        self.assertIn('def Conditions',source)
        self.assertIn('SpecTec.«Copy»',source)
        self.assertIn('> (0 : Nat)',source)

    def test_shared_internal_witness_is_under_both_conditions(self):
        from pbt.property.plan import compile_clause
        from pbt.property import emit as property_emit
        source='''property positive:
 (n : nat)
 true
 -- Copy: n ~> x
 -- if $(x > 0)
'''
        plan=compile_clause(frontend(source,COPY_SPEC),{'schema_version':1})
        contract=property_emit.render_contract(plan,'ClauseContract','ClauseSpec')
        self.assertIn('def Premise (input : Input) : Prop := ∃ («x» : Nat), Conditions input «x»',contract)
        self.assertIn('SpecTec.«Copy»',contract)
        self.assertIn('> (0 : Nat)',contract)

class PropertyBuildTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from pbt.property.clause import build_property
        cls.tmp=tempfile.TemporaryDirectory(prefix='ClauseBuildNative',dir=ROOT/'pbt')
        cls.addClassCleanup(cls.tmp.cleanup)
        cls.root=Path(cls.tmp.name);base='pbt.'+cls.root.name
        (cls.root/'spec.watsup').write_text(COPY_SPEC)
        (cls.root/'property.watsup').write_text(COPY_PROPERTY)
        (cls.root/'config.toml').write_text('schema_version = 1\n[[observations]]\nid = "copy"\nrelation = "Copy"\nobserve = ["%1"]\n')
        template=(ROOT/'examples/ordered/templates/copy_positive_proof.lean.in').read_text()
        (cls.root/'Proof.lean').write_text(template.replace('@CONTRACT@',base+'.Bundle.Contract'))
        cls.bundle=build_property(project=ROOT,spec_paths=[cls.root/'spec.watsup'],
            property_path=cls.root/'property.watsup',config_path=cls.root/'config.toml',
            name='positive',output=cls.root/'Bundle',proof_module=base+'.Proof',
            property_proof='ClauseCopy.property_correct',timeout_seconds=120)

    def test_complete_typed_trace_and_request_provenance(self):
        b=self.bundle
        good=[{'occurrence_id':'condition.0','relation_id':'Copy','input':[3],
               'status':'success','observation':{'%1':3}}]
        self.assertEqual(b.evaluate({'n':3},good),'pass')
        with self.assertRaisesRegex(ValueError,'incomplete trace'):b.evaluate({'n':3},[])
        with self.assertRaisesRegex(ValueError,'observation selectors'):b.evaluate({'n':3},[{**good[0],'observation':{}}])
        with self.assertRaisesRegex(ValueError,'type mismatch'):b.evaluate({'n':3},[{**good[0],'observation':{'%1':'bad'}}])
        with self.assertRaisesRegex(ValueError,'request input'):b.evaluate({'n':3},[{**good[0],'input':[99]}])

    def test_relocated_bundle_and_stale_source_are_rejected(self):
        import shutil
        from pbt.property.clause import load_bundle
        b=self.bundle
        copied=self.root/'Relocated'
        shutil.copytree(b.directory,copied)
        with self.assertRaisesRegex(ValueError,'location|module'):load_bundle(copied)
        path=self.root/'property.watsup';original=path.read_text()
        try:
            path.write_text(original+'\n;; changed\n')
            with self.assertRaisesRegex(ValueError,'stale'):b.request({'n':3},[],0)
        finally:path.write_text(original)


class PropertyEdgeBuildTests(unittest.TestCase):
    def test_pure_property_has_no_external_calls_and_checks_in_al(self):
        from pbt.property.clause import build_property
        with tempfile.TemporaryDirectory(prefix='ClausePureNative',dir=ROOT/'pbt') as tmp:
            folder=Path(tmp);base='pbt.'+folder.name
            (folder/'spec.watsup').write_text('var n : nat\n')
            (folder/'property.watsup').write_text('property pure:\n (n : nat)\n n = n\n')
            (folder/'config.toml').write_text('schema_version = 1\n')
            (folder/'Proof.lean').write_text(f'''import {base}.Bundle.Contract
namespace PureProof
theorem property_correct : {base}.Bundle.Contract.SpecProperty := by
  intro input _
  exact decide_eq_true rfl
end PureProof
''')
            bundle=build_property(project=ROOT,spec_paths=[folder/'spec.watsup'],
                property_path=folder/'property.watsup',config_path=folder/'config.toml',
                name='pure',output=folder/'Bundle',proof_module=base+'.Proof',
                property_proof='PureProof.property_correct',timeout_seconds=120)
            self.assertEqual(bundle.plan['calls'],[])
            self.assertEqual(bundle.evaluate({'n':3},[]),'pass')
            with self.assertRaisesRegex(ValueError,'unknown|request'):
                bundle.request({'n':3},[],0)


if __name__=='__main__':unittest.main()
