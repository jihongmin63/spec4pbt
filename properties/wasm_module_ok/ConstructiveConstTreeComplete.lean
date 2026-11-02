import properties.wasm_module_ok.ConstructiveConstOriginalOperators
import Mathlib.Tactic.ClearExcept
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace properties.wasm_module_ok.ConstructiveConstTreeComplete
open SpecTec properties.wasm_module_ok ConstructiveConstTree ConstructiveGenAudit
open properties.wasm_module_ok.ConstructiveConstBuilders properties.wasm_module_ok.ConstructiveConstAggregateBuilders
open properties.wasm_module_ok.ConstructiveConstTableCore properties.wasm_module_ok.ConstructiveConstTableSeeds properties.wasm_module_ok.ConstructiveConstTableExpand
open properties.wasm_module_ok.ConstructiveConstTableCoverage properties.wasm_module_ok.ConstructiveConstSeedCoverage properties.wasm_module_ok.ConstructiveConstGeneration
open properties.wasm_module_ok.ConstructiveConstOriginalLeaves properties.wasm_module_ok.ConstructiveConstOriginalAggregates properties.wasm_module_ok.ConstructiveConstOriginalOperators

theorem node_cover (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (table : List (Entry c)) (i : instr) (u : valtype) (children : List Tree) (need : List valtype)
    (hs : ConstAdditionalSyntaxValidation.Syntax c i)
    (hi : ∀stack n,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c (.NoEllipses,stack++outputs children) i⟩)
      n (.success (.of (effect need u))) n)
    (hm : ∀n,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Match_resulttype c (outputs children) need⟩)
      n (.success (.of ())) n)
    (hk : ∀t∈children,Good c t) (hc : ∀t∈children,Covers table t) :
    Covers (seeds c hp ++ expand c hr hn table) (.node i u children) := by
  have hcall := hi [] 0
  simp only [List.nil_append] at hcall
  have hsyntax := (ConstSyntaxDecision.syntaxAllowed_iff c i).2 hs
  cases hs with
  | num v =>
    apply covers_mono ?_ (number_node c hp v u children need hcall hm)
    intro e he; simp only [seeds,expand,List.mem_append]; clear * - he; tauto
  | vec v =>
    apply covers_mono ?_ (vector_node c hp v u children need hcall hm)
    intro e he; simp only [seeds,expand,List.mem_append]; clear * - he; tauto
  | refNull ht =>
    apply covers_mono ?_ (null_node c hp ht u children need hcall hm)
    intro e he; simp only [seeds,expand,List.mem_append]; clear * - he; tauto
  | refFunc x =>
    apply covers_mono ?_ (function_node c hp x u children need hcall hm)
    intro e he; simp only [seeds,expand,List.mem_append]; clear * - he; tauto
  | globalGet x t hg =>
    apply covers_mono ?_ (global_node c hp x t hg u children need hcall hm)
    intro e he; simp only [seeds,expand,List.mem_append]; clear * - he; tauto
  | refI31 =>
    apply covers_mono ?_ (i31_node c hr table u children need hcall hm hk hc)
    intro e he; simp only [seeds,expand,List.mem_append]; clear * - he; tauto
  | arithmetic i hop =>
    obtain ⟨op,rfl⟩ : ∃op,i=.BINOP op := by
      simp [ConstArithmeticValidation.arithmeticOps] at hop
      rcases hop with rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨_,rfl⟩
    have hresult := ((ConstInstrDecision.arithmetic_result_iff c _ op _ 0 0).2 ⟨hsyntax,hcall⟩).1
    apply covers_mono ?_ (arithmetic_node c hr table op hop u children need hresult hm hk hc)
    intro e he; simp only [seeds,expand,List.mem_append]; clear * - he; tauto
  | structNew x op =>
    cases op with
    | Explicit =>
      have hresult := ((ConstInstrDecision.struct_explicit_result_iff c _ x _ 0 0).2 ⟨hsyntax,hcall⟩).1
      apply covers_mono ?_ (struct_explicit_node c hr hn table x u children need hresult hm hk hc)
      intro e he; simp only [seeds,expand,List.mem_append]; clear * - he; tauto
    | Implicit =>
      have hresult := ((ConstInstrDecision.struct_implicit_result_iff c _ x _ 0 0).2 ⟨hsyntax,hcall⟩).1
      apply covers_mono ?_ (struct_implicit_node c hp x u children need hresult hm)
      intro e he; simp only [seeds,expand,List.mem_append]; clear * - he; tauto
  | arrayNew x op =>
    cases op with
    | Explicit =>
      have hresult := ((ConstInstrDecision.array_explicit_result_iff c _ x _ 0 0).2 ⟨hsyntax,hcall⟩).1
      apply covers_mono ?_ (array_explicit_node c hr hn table x u children need hresult hm hk hc)
      intro e he; simp only [seeds,expand,List.mem_append]; clear * - he; tauto
    | Implicit =>
      have hresult := ((ConstInstrDecision.array_implicit_result_iff c _ x _ 0 0).2 ⟨hsyntax,hcall⟩).1
      apply covers_mono ?_ (array_implicit_node c hr hn table x u children need hresult hm hk hc)
      intro e he; simp only [seeds,expand,List.mem_append]; clear * - he; tauto
  | arrayNewFixed x count =>
    have hresult := ((ConstInstrDecision.array_fixed_result_iff c _ x count _ 0 0).2 ⟨hsyntax,hcall⟩).1
    apply covers_mono ?_ (array_fixed_node c hr hp hn table x count u children need hresult hm hk hc)
    intro e he; simp only [List.mem_append] at he
    simp only [seeds,expand,List.mem_append]; clear * - he; tauto
  | externConvert op =>
    have hresult := ((ConstInstrDecision.extern_convert_result_iff c _ op _ 0 0).2 ⟨hsyntax,hcall⟩).1
    apply covers_mono ?_ (extern_node c hr table op u children need hresult hm hk hc)
    intro e he; cases op <;> simp only [seeds,expand,List.mem_append] <;> clear * - he <;> tauto

theorem common_round (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (forest : List Tree)
    (h : ∀t∈forest,∃n,Covers (rounds c hr hp hn n) t) :
    ∃n,∀t∈forest,Covers (rounds c hr hp hn n) t := by
  induction forest with
  | nil => exact ⟨0,by simp⟩
  | cons a as ih =>
    obtain ⟨na,ha⟩ := h a (by simp)
    obtain ⟨ns,hs⟩ := ih (fun t ht => h t (by simp [ht]))
    refine ⟨na+ns,?_⟩
    intro t ht
    rcases List.mem_cons.mp ht with rfl|ht
    · exact covers_mono (rounds_monotone c hr hp hn na ns) ha
    · have hm := covers_mono (rounds_monotone c hr hp hn ns na) (hs t ht)
      simpa only [Nat.add_comm ns na] using hm

theorem good_covered (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (tree : Tree) (h : Good c tree) : ∃n,Covers (rounds c hr hp hn n) tree := by
  induction h with
  | node i u children need hs hi hm hk ih =>
    obtain ⟨n,hchildren⟩ := common_round c hr hp hn children ih
    have hnode := node_cover c hr hp hn (rounds c hr hp hn n) i u children need hs hi hm hk hchildren
    refine ⟨n+1,covers_mono ?_ hnode⟩
    intro e he
    rcases List.mem_append.mp he with he|he
    · exact List.mem_append_left _ (by simpa only [Nat.zero_add] using rounds_monotone c hr hp hn 0 n he)
    · exact List.mem_append_right _ he

theorem trees_complete (c : context) (hr : CandidateTypeReady.Ready c)
    (hp : CandidateUniverseReady.Provenance c) (hn : CandidateNestedReady.nestedTableReady c=true)
    (tree : Witness c) : Gen.support (trees c hr hp hn) tree :=
  (trees_support c hr hp hn tree).2 (good_covered c hr hp hn tree.val tree.property)

#print axioms trees_complete
end properties.wasm_module_ok.ConstructiveConstTreeComplete
