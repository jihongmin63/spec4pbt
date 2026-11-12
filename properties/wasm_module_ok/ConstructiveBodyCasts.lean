import properties.wasm_module_ok.ConstructiveBodyTopCoverage
import properties.wasm_module_ok.ConstructiveBodyReferenceCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyCasts
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyIndexedProductions ConstructiveBodyProductionCoverage

theorem testRef_call (c : context) (stack : inferresulttype) (t : ConstructiveBodyTopMetadata.Top c) (nu : SpecTec.null) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«REF.TEST» (.«% %» nu t.heap))⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.RefT (.«% %» .Null t.top)] [.NumT .I32T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«REF.TEST» (.«% %» nu t.heap)) 54 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:54» c stack (.«REF.TEST» (.«% %» nu t.heap))) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:54»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success ((ValtypeValidation.reftype_success_iff c nu t.heap n n).2
    ((HeaptypeValidation.heaptype_success_iff_valid c t.heap n n).2 ⟨t.valid,rfl⟩))
  apply SpecTecExecution.Eval.bind_success (t.call n)
  exact SpecTecExecution.Eval.pure _

def testRef (c : context) (stack : inferresulttype) (env : Env c) (t : ConstructiveBodyTopMetadata.Top c) (nu : SpecTec.null) : Production c stack :=
  fixed c stack env (.NoEllipses,[.RefT (.«% %» .Null t.top)]) (.NoEllipses,[.NumT .I32T])
    (cons_backed .NoEllipses (ConstructiveBodyReferenceMatcher.base_backed c .Null t.top t.baseTop) (nil_backed c .NoEllipses))
    (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses))
    (.«REF.TEST» (.«% %» nu t.heap)) (testRef_call c stack t nu)

theorem castRef_call (c : context) (stack : inferresulttype) (t : ConstructiveBodyTopMetadata.Top c) (nu : SpecTec.null) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«REF.CAST» (.«% %» nu t.heap))⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.RefT (.«% %» .Null t.top)] [.RefT (.«% %» nu t.heap)] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«REF.CAST» (.«% %» nu t.heap)) 55 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:55» c stack (.«REF.CAST» (.«% %» nu t.heap))) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:55»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success ((ValtypeValidation.reftype_success_iff c nu t.heap n n).2
    ((HeaptypeValidation.heaptype_success_iff_valid c t.heap n n).2 ⟨t.valid,rfl⟩))
  apply SpecTecExecution.Eval.bind_success (t.call n)
  exact SpecTecExecution.Eval.pure _

def castRef (c : context) (stack : inferresulttype) (env : Env c) (t : ConstructiveBodyTopMetadata.Top c) (nu : SpecTec.null) : Production c stack :=
  fixed c stack env (.NoEllipses,[.RefT (.«% %» .Null t.top)]) (.NoEllipses,[.RefT (.«% %» nu t.heap)])
    (cons_backed .NoEllipses (ConstructiveBodyReferenceMatcher.base_backed c .Null t.top t.baseTop) (nil_backed c .NoEllipses))
    (cons_backed .NoEllipses (CandidateValMembership.valid_candidate_in_table c _
      ((FiniteValidTypes.validCandidates_spec c _).2 t.valid)) (nil_backed c .NoEllipses))
    (.«REF.CAST» (.«% %» nu t.heap)) (castRef_call c stack t nu)

def all (c : context) (stack : inferresulttype) (env : Env c) : List (Production c stack) :=
  (ConstructiveBodyTopMetadata.all c).flatMap fun t =>
    [testRef c stack env t .Null,testRef c stack env t .NoNull,
     castRef c stack env t .Null,castRef c stack env t .NoNull]

theorem testRef_produces (c : context) (stack : inferresulttype) (env : Env c) (t : ConstructiveBodyTopMetadata.Top c) (nu : SpecTec.null) :
    Produces (testRef c stack env t nu) (.«REF.TEST» (.«% %» nu t.heap)) := by
  unfold Produces testRef fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem testRef_metadata (c : context) (stack : inferresulttype) (env : Env c) (nu : SpecTec.null) (heap : heaptype)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«REF.TEST» (.«% %» nu heap))⟩) n (.success (.of effect)) finish) :
    ∃t∈ConstructiveBodyTopMetadata.all c,t.heap=heap := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«REF.TEST» (.«% %» nu heap)) 54 (by decide) rfl (by decide) effect n finish).1 h
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:54» c stack (.«REF.TEST» (.«% %» nu heap))) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:54» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hvalid tail =>
    have hv := (HeaptypeValidation.heaptype_success_iff_valid c heap _ _).1
      ((ValtypeValidation.reftype_success_iff c nu heap _ _).1 hvalid) |>.1
    cases tail with | bind_success htop tail =>
     exact ConstructiveBodyTopCoverage.all_complete c env.ready heap hv (ConstructiveBodyTopCoverage.not_bot c heap _ _ _ htop)

theorem testRef_original (c : context) (stack : inferresulttype) (env : Env c) (rt : reftype)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«REF.TEST» rt)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«REF.TEST» rt) effect ∧ finish=n := by
  cases rt with | «% %» nu heap =>
   obtain ⟨t,ht,he⟩ := testRef_metadata c stack env nu heap effect n finish h
   apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (testRef c stack env t nu) _ effect n finish
   · apply List.mem_flatMap.mpr
     exact ⟨t,ht,by cases nu <;> simp⟩
   · simpa only [he] using testRef_produces c stack env t nu
   · exact h

theorem castRef_produces (c : context) (stack : inferresulttype) (env : Env c) (t : ConstructiveBodyTopMetadata.Top c) (nu : SpecTec.null) :
    Produces (castRef c stack env t nu) (.«REF.CAST» (.«% %» nu t.heap)) := by
  unfold Produces castRef fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem castRef_metadata (c : context) (stack : inferresulttype) (env : Env c) (nu : SpecTec.null) (heap : heaptype)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«REF.CAST» (.«% %» nu heap))⟩) n (.success (.of effect)) finish) :
    ∃t∈ConstructiveBodyTopMetadata.all c,t.heap=heap := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«REF.CAST» (.«% %» nu heap)) 55 (by decide) rfl (by decide) effect n finish).1 h
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:55» c stack (.«REF.CAST» (.«% %» nu heap))) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:55» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hvalid tail =>
    have hv := (HeaptypeValidation.heaptype_success_iff_valid c heap _ _).1
      ((ValtypeValidation.reftype_success_iff c nu heap _ _).1 hvalid) |>.1
    cases tail with | bind_success htop tail =>
     exact ConstructiveBodyTopCoverage.all_complete c env.ready heap hv (ConstructiveBodyTopCoverage.not_bot c heap _ _ _ htop)

theorem castRef_original (c : context) (stack : inferresulttype) (env : Env c) (rt : reftype)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«REF.CAST» rt)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«REF.CAST» rt) effect ∧ finish=n := by
  cases rt with | «% %» nu heap =>
   obtain ⟨t,ht,he⟩ := castRef_metadata c stack env nu heap effect n finish h
   apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (castRef c stack env t nu) _ effect n finish
   · apply List.mem_flatMap.mpr
     exact ⟨t,ht,by cases nu <;> simp⟩
   · simpa only [he] using castRef_produces c stack env t nu
   · exact h

#print axioms testRef_original
#print axioms castRef_original
end properties.wasm_module_ok.ConstructiveBodyCasts
