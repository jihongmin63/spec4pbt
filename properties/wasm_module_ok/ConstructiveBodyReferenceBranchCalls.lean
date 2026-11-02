import properties.wasm_module_ok.ConstructiveBodyNonemptyLabels
import properties.wasm_module_ok.ConstructiveBodyReferenceDifference
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyReferenceBranchCalls
open SpecTec properties.wasm_module_ok ConstructiveBodyNonemptyLabels

theorem onNull (c : context) (stack : inferresulttype) (e : ConstructiveBodyLookup.Entry c.LABELS)
    (nu : SpecTec.null) (heap : heaptype)
    (hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap)) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.BR_ON_NULL e.index)⟩)
      n (.success (.of (ConstructiveBodyControl.effect (e.value++[.RefT (.«% %» .Null heap)])
        (e.value++[.RefT (.«% %» .NoNull heap)]) []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.BR_ON_NULL e.index) 11 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:11» c stack (.BR_ON_NULL e.index)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:11»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (PeekRefDecision.peek_ref_total_of_some 0 stack (.«% %» nu heap) n hp)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp e.lookup).1)
  rw [e.lookup]
  exact SpecTecExecution.Eval.pure _

theorem onNonNull (c : context) (stack : inferresulttype) (label : Label c)
    (nu : SpecTec.null) (heap : heaptype)
    (hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap))
    (hm : ∀s,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,SpecTecCall.«$match_valtype» c.TYPES (.RefT (.«% %» .NoNull heap)) label.last⟩)
      s (.success (.of true)) s) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.BR_ON_NON_NULL label.entry.index)⟩)
      n (.success (.of (ConstructiveBodyControl.effect (label.front++[.RefT (.«% %» .Null heap)]) label.front []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.BR_ON_NON_NULL label.entry.index) 12 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:12» c stack (.BR_ON_NON_NULL label.entry.index)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:12»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (PeekRefDecision.peek_ref_total_of_some 0 stack (.«% %» nu heap) n hp)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp label.entry.lookup).1)
  simp only [label.entry.lookup]
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true label.nonempty)
  rw [label.converted]
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp only [decide_eq_true_eq]; exact Int.natCast_nonneg _))
  simp only [Int.toNat?,List.drop_zero]
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.orElse_success
    (SpecTecExecution.Eval.guard_true (show 0+label.width≤label.entry.value.length from by have h:=label.bound; omega)))
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true label.bound)
  rw [label.lookupLast]
  apply SpecTecExecution.Eval.bind_success (hm n)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  exact SpecTecExecution.Eval.pure _

theorem onCast (c : context) (stack : inferresulttype) (label : Label c) (r1 r2 : reftype)
    (h1 : ∀s,SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨Unit,SpecTecCall.Reftype_ok c r1⟩) s (.success (.of ())) s)
    (h2 : ∀s,SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨Unit,SpecTecCall.Reftype_ok c r2⟩) s (.success (.of ())) s)
    (hr : ∀s,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,SpecTecCall.«$match_reftype» c.TYPES r2 r1⟩) s (.success (.of true)) s)
    (hm : ∀s,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,SpecTecCall.«$match_valtype» c.TYPES (.RefT r2) label.last⟩) s (.success (.of true)) s)
    (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.BR_ON_CAST label.entry.index r1 r2)⟩)
      n (.success (.of (ConstructiveBodyControl.effect (label.front++[.RefT r1]) (label.front++[.RefT (ConstructiveBodyReferenceDifference.difference r1 r2)]) []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.BR_ON_CAST label.entry.index r1 r2) 13 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:13» c stack (.BR_ON_CAST label.entry.index r1 r2)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:13»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (h1 n)
  apply SpecTecExecution.Eval.bind_success (h2 n)
  apply SpecTecExecution.Eval.bind_success (hr n)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp label.entry.lookup).1)
  simp only [label.entry.lookup]
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true label.nonempty)
  rw [label.converted]
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp only [decide_eq_true_eq]; exact Int.natCast_nonneg _))
  simp only [Int.toNat?,List.drop_zero]
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.orElse_success
    (SpecTecExecution.Eval.guard_true (show 0+label.width≤label.entry.value.length from by have h:=label.bound; omega)))
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true label.bound)
  rw [label.lookupLast]
  apply SpecTecExecution.Eval.bind_success (hm n)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (ConstructiveBodyReferenceDifference.total r1 r2 n)
  exact SpecTecExecution.Eval.pure _

theorem onCastFail (c : context) (stack : inferresulttype) (label : Label c) (r1 r2 : reftype)
    (h1 : ∀s,SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨Unit,SpecTecCall.Reftype_ok c r1⟩) s (.success (.of ())) s)
    (h2 : ∀s,SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨Unit,SpecTecCall.Reftype_ok c r2⟩) s (.success (.of ())) s)
    (hr : ∀s,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,SpecTecCall.«$match_reftype» c.TYPES r2 r1⟩) s (.success (.of true)) s)
    (hm : ∀s,SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,SpecTecCall.«$match_valtype» c.TYPES (.RefT (ConstructiveBodyReferenceDifference.difference r1 r2)) label.last⟩) s (.success (.of true)) s)
    (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.BR_ON_CAST_FAIL label.entry.index r1 r2)⟩)
      n (.success (.of (ConstructiveBodyControl.effect (label.front++[.RefT r1]) (label.front++[.RefT r2]) []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.BR_ON_CAST_FAIL label.entry.index r1 r2) 14 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:14» c stack (.BR_ON_CAST_FAIL label.entry.index r1 r2)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:14»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (h1 n)
  apply SpecTecExecution.Eval.bind_success (h2 n)
  apply SpecTecExecution.Eval.bind_success (ConstructiveBodyReferenceDifference.total r1 r2 n)
  apply SpecTecExecution.Eval.bind_success (hr n)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp label.entry.lookup).1)
  simp only [label.entry.lookup]
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true label.nonempty)
  rw [label.converted]
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp only [decide_eq_true_eq]; exact Int.natCast_nonneg _))
  simp only [Int.toNat?,List.drop_zero]
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.orElse_success
    (SpecTecExecution.Eval.guard_true (show 0+label.width≤label.entry.value.length from by have h:=label.bound; omega)))
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true label.bound)
  rw [label.lookupLast]
  apply SpecTecExecution.Eval.bind_success (hm n)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  exact SpecTecExecution.Eval.pure _

#print axioms onNonNull
#print axioms onCastFail
end properties.wasm_module_ok.ConstructiveBodyReferenceBranchCalls
