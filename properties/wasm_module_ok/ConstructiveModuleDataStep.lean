import properties.wasm_module_ok.ConstructiveModuleModes
import properties.wasm_module_ok.ConstructiveModuleStrings
import properties.wasm_module_ok.ConstructiveModuleElemDataRules
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleDataStep
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyEnvironment ConstructiveConstTableCore

structure Step (c : context) where
  item : SpecTec.data
  after : context
  env : Env after
  correct : ∀n,Eval specTecProgram (.call ⟨context,SpecTecCall.Data_ok c item⟩) n (.success (.of after)) n

def step (c : context) (env : Env c) (mode : ConstructiveModuleModes.DataMode c) (text : String) : Step c :=
  ⟨⟨text,mode.val⟩,{c with DATAS:=c.DATAS++[datatype.OK]},ConstructiveModuleEnvironment.withDatas c env _,
    fun n => ConstructiveModuleElemDataRules.data c _ n (mode.property n)⟩
def one (c : context) (env : Env c) : Audited (Step c) :=
  (ConstructiveModuleModes.data c env).bind fun mode =>
    (⟨ConstructiveModuleStrings.strings,ConstructiveModuleStrings.strings_audit⟩ : Audited String).map (step c env mode)

theorem complete (c out : context) (env : Env c) (item : SpecTec.data) (n finish : Nat)
    (h : Eval specTecProgram (.call ⟨context,SpecTecCall.Data_ok c item⟩) n (.success (.of out)) finish) :
    ∃s : Step c,Gen.support (one c env).generator s ∧ s.item=item ∧ s.after=out := by
  obtain ⟨hm,ho⟩ := ConstructiveModuleElemDataRules.data_original c out item n finish h
  obtain ⟨mode,hmode,he⟩ := ConstructiveModuleModes.data_complete c env item.DMODE n finish hm
  refine ⟨step c env mode item.DINIT,⟨mode,hmode,item.DINIT,ConstructiveModuleStrings.strings_complete _,rfl⟩,?_,ho.symm⟩
  cases item;simp_all [step]
#print axioms complete
end properties.wasm_module_ok.ConstructiveModuleDataStep
