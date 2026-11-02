import properties.wasm_module_ok.ConstExpressionDecision
import properties.wasm_module_ok.ElemDataConstValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ElemInitDecision

def elemInitValid (c : SpecTec.context) (rt : SpecTec.reftype)
    (inits : List SpecTec.const) : Bool :=
  inits.all (ConstExpressionDecision.constantExpressionResult c (.RefT rt))

theorem elem_iter_nil_success_iff
    (c : SpecTec.context) (rt : SpecTec.reftype)
    (start finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.«Elem_ok:rule:iter:0» c rt []⟩)
      start (.success (.of ())) finish ↔ finish = start := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«Elem_ok:rule:iter:0_clauses» c rt []))
        start (.success (.of ())) finish at hbody
      cases hbody with
      | orElse_success hclause =>
        unfold SpecTec.«Elem_ok:rule:iter:0:clause:0» at hclause
        cases hclause
        rfl
      | orElse_unmatch hfailedSupply htail =>
        restore_supply hfailedSupply at htail
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTecExecution.tryClauses
            [SpecTec.«Elem_ok:rule:iter:0:clause:1» c rt []])
          start (.success (.of ())) finish at htail
        cases htail with
        | orElse_success hclause =>
          unfold SpecTec.«Elem_ok:rule:iter:0:clause:1» at hclause
          cases hclause
        | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone
  · intro hsame
    subst finish
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«Elem_ok:rule:iter:0_clauses» c rt []))
      start (.success (.of ())) start
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Elem_ok:rule:iter:0:clause:0» c rt [])
      start (.success (.of ())) start
    unfold SpecTec.«Elem_ok:rule:iter:0:clause:0»
    exact SpecTecExecution.Eval.pure ()

theorem elem_init_valid_iff_iter
    (c : SpecTec.context) (rt : SpecTec.reftype)
    (inits : List SpecTec.const) (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (htarget : CandidateValMatch.InTableVal c (.RefT rt)) :
    elemInitValid c rt inits = true ∧ finish = start ↔
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.«Elem_ok:rule:iter:0»
          c rt inits⟩)
        start (.success (.of ())) finish := by
  induction inits generalizing start finish with
  | nil =>
      simpa [elemInitValid] using
        (elem_iter_nil_success_iff c rt start finish).symm
  | cons init rest ih =>
      constructor
      · rintro ⟨hvalid, hfinish⟩
        have hparts :
            ConstExpressionDecision.constantExpressionResult
                c (.RefT rt) init = true ∧
              elemInitValid c rt rest = true := by
          simpa only [elemInitValid, List.all_cons, Bool.and_eq_true]
            using hvalid
        obtain ⟨hhead, htail⟩ := hparts
        subst finish
        apply (ElemDataConstValidation.elem_iter_cons_success_iff
          c rt init rest start start).2
        refine ⟨start, ?_, ?_⟩
        · exact (ConstExpressionDecision.constant_expression_result_iff_const_ok_any_counters
            c (.RefT rt) init start start hready hprov hnested htarget).1
            ⟨hhead, rfl⟩
        · exact (ih start start).1 ⟨htail, rfl⟩
      · intro hcall
        obtain ⟨middle, hhead, htail⟩ :=
          (ElemDataConstValidation.elem_iter_cons_success_iff
            c rt init rest start finish).1 hcall
        obtain ⟨hheadValid, hmiddle⟩ :=
          (ConstExpressionDecision.constant_expression_result_iff_const_ok_any_counters
            c (.RefT rt) init start middle
            hready hprov hnested htarget).2 hhead
        obtain ⟨htailValid, hfinish⟩ := (ih middle finish).2 htail
        have hvalid : elemInitValid c rt (init :: rest) = true := by
          simpa only [elemInitValid, List.all_cons, Bool.and_eq_true]
            using And.intro hheadValid htailValid
        exact ⟨hvalid, hfinish.trans hmiddle⟩

end properties.wasm_module_ok.ElemInitDecision
