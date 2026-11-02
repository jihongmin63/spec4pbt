import properties.wasm_module_ok.ConstructiveConstOperatorCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstOriginalLeaves
open SpecTec properties.wasm_module_ok ConstructiveConstTree ConstructiveGenAudit
open properties.wasm_module_ok.ConstructiveConstBuilders properties.wasm_module_ok.ConstructiveConstAggregateBuilders
open properties.wasm_module_ok.ConstructiveConstTableCore properties.wasm_module_ok.ConstructiveConstTableSeeds properties.wasm_module_ok.ConstructiveConstTableExpand
open properties.wasm_module_ok.ConstructiveConstTableCoverage properties.wasm_module_ok.ConstructiveConstSeedCoverage properties.wasm_module_ok.ConstructiveConstOperatorCoverage

theorem effect_inj (a b : List valtype) (u v : valtype)
    (h : effect a u=effect b v) : a=b ∧ u=v := by
  have hi := congrArg (fun e : inferinstrtype => e.1.INS.2) h
  have ho := congrArg (fun e : inferinstrtype => e.1.OUTS.2) h
  exact ⟨hi,by simpa [effect] using ho⟩

theorem empty_children (c : context) (children : List Tree)
    (hm : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Match_resulttype c (outputs children) []⟩)
      0 (.success (.of ())) 0) : children=[] := by
  have hlen := (MatchResulttypeValidation.match_resulttype_success_iff c (outputs children) [] 0 0).1 hm |>.1
  exact List.eq_nil_of_length_eq_zero (by simpa [outputs] using hlen.symm)

theorem number_node (c : context) (hp : CandidateUniverseReady.Provenance c)
    (v : num_) (u : valtype) (children : List Tree) (need : List valtype)
    (hi : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c (.NoEllipses,outputs children) (.CONST v)⟩)
      0 (.success (.of (effect need u))) 0)
    (hm : ∀n,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Match_resulttype c (outputs children) need⟩)
      n (.success (.of ())) n) :
    Covers (literalEntries c hp) (.node (.CONST v) u children) := by
  have hr := (ConstInstrDecision.numeric_literal_result_iff c _ v _ 0 0).2 hi |>.1
  have he : effect [] (.NumT (ConstLiteralEffect.numericType v))=effect need u := Option.some.inj hr
  obtain ⟨hn,hu⟩ := effect_inj _ _ _ _ he
  subst need; subst u
  have hc := empty_children c children (hm 0)
  subst children
  exact number_cover c hp v

theorem vector_node (c : context) (hp : CandidateUniverseReady.Provenance c)
    (v : vec_) (u : valtype) (children : List Tree) (need : List valtype)
    (hi : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c (.NoEllipses,outputs children) (.«VEC.CONST» v)⟩)
      0 (.success (.of (effect need u))) 0)
    (hm : ∀n,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Match_resulttype c (outputs children) need⟩)
      n (.success (.of ())) n) :
    Covers (literalEntries c hp) (.node (.«VEC.CONST» v) u children) := by
  have hr := (ConstInstrDecision.vector_literal_result_iff c _ v _ 0 0).2 hi |>.1
  have he : effect [] (.VecT .V128T)=effect need u := Option.some.inj hr
  obtain ⟨hn,hu⟩ := effect_inj _ _ _ _ he
  subst need; subst u
  have hc := empty_children c children (hm 0)
  subst children
  exact vector_cover c hp v

theorem null_node (c : context) (hp : CandidateUniverseReady.Provenance c)
    (ht : heaptype) (u : valtype) (children : List Tree) (need : List valtype)
    (hi : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c (.NoEllipses,outputs children) (.«REF.NULL» ht)⟩)
      0 (.success (.of (effect need u))) 0)
    (hm : ∀n,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Match_resulttype c (outputs children) need⟩)
      n (.success (.of ())) n) :
    Covers (nullEntries c hp) (.node (.«REF.NULL» ht) u children) := by
  obtain ⟨hh,he,_⟩ := (ConstRefNullDispatch.ref_null_dispatch_iff c _ ht _ 0 0).1 hi
  obtain ⟨hn,hu⟩ := effect_inj _ _ _ _ he
  subst need; subst u
  have hc := empty_children c children (hm 0)
  subst children
  exact null_cover c hp ht hh

theorem function_node (c : context) (hp : CandidateUniverseReady.Provenance c)
    (x : Nat) (u : valtype) (children : List Tree) (need : List valtype)
    (hi : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c (.NoEllipses,outputs children) (.«REF.FUNC» x)⟩)
      0 (.success (.of (effect need u))) 0)
    (hm : ∀n,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Match_resulttype c (outputs children) need⟩)
      n (.success (.of ())) n) :
    Covers (functionEntries c hp) (.node (.«REF.FUNC» x) u children) := by
  obtain ⟨dt,hget,href,he,_⟩ := (ConstRefFuncEffect.ref_func_instruction_iff c _ x _ 0 0).1 hi
  obtain ⟨hn,hu⟩ := effect_inj _ _ _ _ he
  subst need; subst u
  have hc := empty_children c children (hm 0)
  subst children
  exact function_cover c hp x dt hget href

theorem global_node (c : context) (hp : CandidateUniverseReady.Provenance c)
    (x : Nat) (ty : valtype) (hget : c.GLOBALS[x]?=some (.GlobalT .Cons ty))
    (u : valtype) (children : List Tree) (need : List valtype)
    (hi : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c (.NoEllipses,outputs children) (.«GLOBAL.GET» x)⟩)
      0 (.success (.of (effect need u))) 0)
    (hm : ∀n,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Match_resulttype c (outputs children) need⟩)
      n (.success (.of ())) n) :
    Covers (globalEntries c hp) (.node (.«GLOBAL.GET» x) u children) := by
  have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by intro req a b h; cases h
  have he' := (SpecTecExecution.eval_deterministic hdet hi (ConstGlobalGetDispatch.global_get_dispatch_total c _ x .Cons ty 0 hget)).1
  have he : effect need u=effect [] ty := by cases he'; rfl
  obtain ⟨hn,hu⟩ := effect_inj _ _ _ _ he
  subst need; subst u
  have hc := empty_children c children (hm 0)
  subst children
  exact global_cover c hp x ty hget

#print axioms number_node
#print axioms global_node
end properties.wasm_module_ok.ConstructiveConstOriginalLeaves
