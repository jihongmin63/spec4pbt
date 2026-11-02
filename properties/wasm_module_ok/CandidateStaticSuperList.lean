import properties.wasm_module_ok.CandidateStaticSuperCheck
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateStaticSuperList

/-- Exact finite check for all supertype members in the closing subtype pass. -/
def staticSuperChecks (c : SpecTec.context) (x : SpecTec.typeidx)
    (strt : SpecTec.strtype) : List SpecTec.heaptype → Bool
  | [] => true
  | ht :: hts =>
      CandidateStaticSuperCheck.staticSuperCheck c x strt ht &&
        staticSuperChecks c x strt hts

theorem iter0_success_iff_checks
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (sourceFin : SpecTec.final)
    (sourceHts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (hts : List SpecTec.heaptype)
    (subStart subFinish n finish : Nat)
    (hsub : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Subtype_ok c
          (.SubT sourceFin sourceHts strt)⟩)
      subStart (.success (.of ())) subFinish)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (hready : CandidateTypeReady.Ready c) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Subtype_sub_ok:rule:iter:0» c x strt hts⟩)
      n (.success (.of ())) finish ↔
    staticSuperChecks c x strt hts = true ∧ finish = n := by
  induction hts generalizing n finish with
  | nil =>
      constructor
      · intro h
        obtain ⟨_, hsupply⟩ :=
          properties.wasm_module_ok.Execution.eval_deterministic h
            (CandidateSupertypeIter.iter0_nil_success c x strt n)
        exact ⟨rfl, hsupply⟩
      · rintro ⟨_, rfl⟩
        exact CandidateSupertypeIter.iter0_nil_success c x strt finish
  | cons ht hts ih =>
      constructor
      · intro h
        obtain ⟨middle, hhead, hrest⟩ :=
          (CandidateSupertypeIter.iter0_cons_success_iff
            c x strt ht hts n finish).1 h
        obtain ⟨hcheck, hmiddle⟩ :=
          (CandidateStaticSuperCheck.static_super_check_success_iff
            c x sourceFin sourceHts strt ht
            subStart subFinish n middle hsub hnested hready).1 hhead
        obtain ⟨hchecks, hsupply⟩ :=
          (ih middle finish).1 hrest
        subst middle
        exact ⟨by simp [staticSuperChecks, hcheck, hchecks], hsupply⟩
      · rintro ⟨hall, rfl⟩
        have hparts :
            CandidateStaticSuperCheck.staticSuperCheck c x strt ht = true ∧
            staticSuperChecks c x strt hts = true := by
          simpa [staticSuperChecks] using hall
        obtain ⟨hhead, hrest⟩ := hparts
        apply (CandidateSupertypeIter.iter0_cons_success_iff
          c x strt ht hts finish finish).2
        exact ⟨finish,
          (CandidateStaticSuperCheck.static_super_check_success_iff
            c x sourceFin sourceHts strt ht
            subStart subFinish finish finish hsub hnested hready).2
              ⟨hhead, rfl⟩,
          (ih finish finish).2 ⟨hrest, rfl⟩⟩

theorem subtype_sub_success_iff_checks
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype)
    (subStart subFinish n finish : Nat)
    (hsub : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Subtype_ok c (.SubT fin hts strt)⟩)
      subStart (.success (.of ())) subFinish)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (hready : CandidateTypeReady.Ready c) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Subtype_sub_ok c x (.SubT fin hts strt)⟩)
      n (.success (.of ())) finish ↔
    staticSuperChecks c x strt hts = true ∧ finish = n := by
  rw [CandidateSupertypeIter.subtype_sub_success_iff_iter0]
  exact iter0_success_iff_checks c x fin hts strt hts
    subStart subFinish n finish hsub hnested hready

end properties.wasm_module_ok.CandidateStaticSuperList
