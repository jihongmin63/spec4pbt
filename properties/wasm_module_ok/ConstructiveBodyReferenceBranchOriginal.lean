import properties.wasm_module_ok.ConstructiveBodyValidReferences
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyReferenceBranchOriginal
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyNonemptyLabels

theorem onNull (c : context) (stack : inferresulttype) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.BR_ON_NULL x)⟩) n (.success (.of effect)) finish) :
    ∃(e : ConstructiveBodyLookup.Entry c.LABELS) (nu : SpecTec.null) (heap : heaptype),e.index=x ∧
      PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap) := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.BR_ON_NULL x) 11 (by decide) rfl (by decide) effect n finish).1 h
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:11» c stack (.BR_ON_NULL x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:11» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hp tail =>
    rename_i mid rt
    have hpeek := (PeekRefDecision.peek_ref_success_iff_result 0 stack rt _ _).1 hp |>.1
    cases rt with | «% %» nu heap =>
     cases tail with | bind_success hx tail =>
      cases hx with | guard_true hb =>
       exact ⟨⟨x,c.LABELS[x],List.getElem?_eq_getElem hb⟩,nu,heap,rfl,hpeek⟩

theorem onNonNull (c : context) (stack : inferresulttype) (env : Env c) (hb : StackBacked c stack)
    (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.BR_ON_NON_NULL x)⟩) n (.success (.of effect)) finish) :
    ∃(label : Label c) (nu : SpecTec.null) (heap : heaptype),label.entry.index=x ∧
      PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap) ∧
      CandidateValMatch.candidateValMatch c (.RefT (.«% %» .NoNull heap)) label.last=true := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.BR_ON_NON_NULL x) 12 (by decide) rfl (by decide) effect n finish).1 h
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:12» c stack (.BR_ON_NON_NULL x)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:12» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hp tail =>
    rename_i mid rt
    have hpeek := (PeekRefDecision.peek_ref_success_iff_result 0 stack rt _ _).1 hp |>.1
    cases rt with | «% %» nu heap =>
     cases tail with | bind_success hx tail =>
      cases hx
      cases hx : c.LABELS[x]? with
      | none => rw [hx] at tail; cases tail
      | some ts =>
        simp only [hx] at tail
        cases tail with | bind_success hpos tail =>
         cases hpos with | guard_true hpos =>
          let label : Label c := ⟨⟨x,ts,hx⟩,hpos⟩
          have hc : Int.ofNat ts.length-Int.ofNat 1=Int.ofNat label.width := label.converted
          rw [hc] at tail
          cases tail with | bind_success hg tail =>
           cases hg
           simp only [Int.toNat?,List.drop_zero] at tail
           cases tail with | bind_success hrequire tail =>
            cases tail with | bind_success hbound tail =>
             cases hbound
             rw [label.lookupLast] at tail
             cases tail with | bind_success hmatch tail =>
              cases tail with | bind_success hg tail =>
               cases hg with | guard_true htrue =>
                have hm := (CandidateValMatch.candidate_val_match_iff c (.RefT (.«% %» .NoNull heap)) label.last _ _ _ env.ready
                  (ConstructiveBodyReferenceProductions.retype c nu .NoNull heap (ConstructiveBodyReferenceProductions.peek_backed c stack hb nu heap hpeek))
                  (label.lastBacked env)).1 hmatch
                exact ⟨label,nu,heap,rfl,hpeek,hm.1.symm.trans htrue⟩

private theorem ref_valid (c : context) (r : reftype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body (.call ⟨Unit,Call.Reftype_ok c r⟩) n (.success (.of ())) finish) :
    ValtypeValidation.valtypeValid c (.RefT r)=true := by
  cases r with | «% %» nu heap =>
   exact (HeaptypeValidation.heaptype_success_iff_valid c heap n finish).1
     ((ValtypeValidation.reftype_success_iff c nu heap n finish).1 h) |>.1

private theorem difference_exact (a b actual : reftype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body (.call ⟨reftype,Call.«$diff_reftype» a b⟩) n (.success (.of actual)) finish) :
    actual=ConstructiveBodyReferenceDifference.difference a b := by
  have he := (properties.wasm_module_ok.Execution.eval_deterministic h (ConstructiveBodyReferenceDifference.total a b n)).1
  cases he
  rfl

theorem onCast (c : context) (stack : inferresulttype) (env : Env c)
    (x : Nat) (r1 r2 : reftype) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.BR_ON_CAST x r1 r2)⟩) n (.success (.of effect)) finish) :
    ∃(label : Label c) (a b : ConstructiveBodyValidReferences.Ref c),label.entry.index=x ∧ a.value=r1 ∧ b.value=r2 ∧
      ConstructiveBodyReferenceMatcher.refMatch c b.value a.value=true ∧
      CandidateValMatch.candidateValMatch c (.RefT b.value) label.last=true := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.BR_ON_CAST x r1 r2) 13 (by decide) rfl (by decide) effect n finish).1 h
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:13» c stack (.BR_ON_CAST x r1 r2)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:13» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success h1 tail =>
    let a : ConstructiveBodyValidReferences.Ref c := ⟨r1,ref_valid c r1 _ _ h1⟩
    cases tail with | bind_success h2 tail =>
     let b : ConstructiveBodyValidReferences.Ref c := ⟨r2,ref_valid c r2 _ _ h2⟩
     cases tail with | bind_success hr tail =>
      cases tail with | bind_success hg tail =>
       cases hg with | guard_true htrue =>
        have hrm := (ConstructiveBodyReferenceMatcher.exact_call c r2 r1 _ _ _ env.ready b.backed a.backed).1 hr
        have hrtrue := hrm.1.symm.trans htrue
        cases tail with | bind_success hx tail =>
         cases hx
         cases hx : c.LABELS[x]? with
         | none => rw [hx] at tail; cases tail
         | some ts =>
           simp only [hx] at tail
           cases tail with | bind_success hpos tail =>
            cases hpos with | guard_true hpos =>
             let label : Label c := ⟨⟨x,ts,hx⟩,hpos⟩
             have hc : Int.ofNat ts.length-Int.ofNat 1=Int.ofNat label.width := label.converted
             rw [hc] at tail
             cases tail with | bind_success hg tail =>
              cases hg
              simp only [Int.toNat?,List.drop_zero] at tail
              cases tail with | bind_success hrequire tail =>
               cases tail with | bind_success hbound tail =>
                cases hbound
                rw [label.lookupLast] at tail
                cases tail with | bind_success hmatch tail =>
                 cases tail with | bind_success hg tail =>
                  cases hg with | guard_true htrue =>
                   have hm := (CandidateValMatch.candidate_val_match_iff c (.RefT b.value) label.last _ _ _ env.ready
                     b.backed (label.lastBacked env)).1 hmatch
                   exact ⟨label,a,b,rfl,rfl,rfl,hrtrue,hm.1.symm.trans htrue⟩

theorem onCastFail (c : context) (stack : inferresulttype) (env : Env c)
    (x : Nat) (r1 r2 : reftype) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.BR_ON_CAST_FAIL x r1 r2)⟩) n (.success (.of effect)) finish) :
    ∃(label : Label c) (a b : ConstructiveBodyValidReferences.Ref c),label.entry.index=x ∧ a.value=r1 ∧ b.value=r2 ∧
      ConstructiveBodyReferenceMatcher.refMatch c b.value a.value=true ∧
      CandidateValMatch.candidateValMatch c (.RefT (ConstructiveBodyReferenceDifference.difference a.value b.value)) label.last=true := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.BR_ON_CAST_FAIL x r1 r2) 14 (by decide) rfl (by decide) effect n finish).1 h
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:14» c stack (.BR_ON_CAST_FAIL x r1 r2)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:14» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success h1 tail =>
    let a : ConstructiveBodyValidReferences.Ref c := ⟨r1,ref_valid c r1 _ _ h1⟩
    cases tail with | bind_success h2 tail =>
     let b : ConstructiveBodyValidReferences.Ref c := ⟨r2,ref_valid c r2 _ _ h2⟩
     cases tail with | bind_success hdiff tail =>
      rw [difference_exact r1 r2 _ _ _ hdiff] at tail
      cases tail with | bind_success hr tail =>
       cases tail with | bind_success hg tail =>
        cases hg with | guard_true htrue =>
         have hrm := (ConstructiveBodyReferenceMatcher.exact_call c r2 r1 _ _ _ env.ready b.backed a.backed).1 hr
         have hrtrue := hrm.1.symm.trans htrue
         cases tail with | bind_success hx tail =>
          cases hx
          cases hx : c.LABELS[x]? with
          | none => rw [hx] at tail; cases tail
          | some ts =>
            simp only [hx] at tail
            cases tail with | bind_success hpos tail =>
             cases hpos with | guard_true hpos =>
              let label : Label c := ⟨⟨x,ts,hx⟩,hpos⟩
              have hc : Int.ofNat ts.length-Int.ofNat 1=Int.ofNat label.width := label.converted
              rw [hc] at tail
              cases tail with | bind_success hg tail =>
               cases hg
               simp only [Int.toNat?,List.drop_zero] at tail
               cases tail with | bind_success hrequire tail =>
                cases tail with | bind_success hbound tail =>
                 cases hbound
                 rw [label.lookupLast] at tail
                 cases tail with | bind_success hmatch tail =>
                  cases tail with | bind_success hg tail =>
                   cases hg with | guard_true htrue =>
                    have hm := (CandidateValMatch.candidate_val_match_iff c (.RefT (ConstructiveBodyReferenceDifference.difference a.value b.value)) label.last _ _ _ env.ready
                      (ConstructiveBodyReferenceDifference.backed c _ _ a.backed) (label.lastBacked env)).1 hmatch
                    exact ⟨label,a,b,rfl,rfl,rfl,hrtrue,hm.1.symm.trans htrue⟩

#print axioms onNonNull
#print axioms onCastFail
end properties.wasm_module_ok.ConstructiveBodyReferenceBranchOriginal
