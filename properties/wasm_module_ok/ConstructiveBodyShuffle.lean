import properties.wasm_module_ok.ConstructiveBodyCertifiedChoice
import properties.wasm_module_ok.ConstructiveLists
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyShuffle
open SpecTec properties.wasm_module_ok ConstructiveConstTableCore

theorem indices_call (xs : List Nat) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,SpecTecCall.«$check_lane_index» xs⟩)
      n (.success (.of (xs.all (fun x => decide (x<32))))) n := by
  induction xs with
  | nil =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«$check_lane_index_clauses» []) ()) n (.success (.of true)) n
    apply SpecTecExecution.firstSuccess_cons_success
    unfold SpecTec.«$check_lane_index:clause:0»
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
  | cons x xs ih =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«$check_lane_index_clauses» (x::xs)) ()) n (.success (.of _)) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · unfold SpecTec.«$check_lane_index:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp))
    by_cases hx : x<32
    · apply SpecTecExecution.firstSuccess_cons_success
      unfold SpecTec.«$check_lane_index:clause:1»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp))
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true hx)
      apply SpecTecExecution.Eval.bind_success ih
      simpa [hx] using (SpecTecExecution.Eval.pure (xs.all (fun x => decide (x<32))) (program:=SpecTec.specTecProgram) (n:=n))
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · unfold SpecTec.«$check_lane_index:clause:1»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp))
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false hx)
      apply SpecTecExecution.firstSuccess_cons_success
      unfold SpecTec.«$check_lane_index:clause:2»
      simpa [hx] using (SpecTecExecution.Eval.pure false (program:=SpecTec.specTecProgram) (n:=n))

theorem indices_exact (xs : List Nat) (b : Bool) (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,SpecTecCall.«$check_lane_index» xs⟩) n (.success (.of b)) finish ↔
    b=xs.all (fun x => decide (x<32)) ∧ finish=n := by
  constructor
  · intro h
    obtain ⟨he,hn⟩ := SpecTecExecution.eval_deterministic (by intro request a b h; cases h) h (indices_call xs n)
    cases he; exact ⟨rfl,hn⟩
  · rintro ⟨rfl,hn⟩; subst finish; exact indices_call xs n

def indices : Audited {xs : List Nat // ∀x∈xs,x<32} :=
  (⟨ConstructiveLists.all (ConstructiveBodyChoice.index 31).generator,
    ConstructiveLists.all_audit _ (ConstructiveBodyChoice.index 31).audit⟩ : Audited (List (Fin 32))).map fun xs =>
      ⟨xs.map Fin.val,by
        intro x hx
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
        exact i.isLt⟩

theorem indices_complete (xs : List Nat) (h : ∀x∈xs,x<32) :
    Gen.support indices.generator ⟨xs,h⟩ := by
  let is : List (Fin 32) := xs.attach.map fun x => ⟨x.val,h x.val x.property⟩
  have he : is.map Fin.val=xs := by simp [is,List.map_map]
  simp only [indices,Audited.map,Gen.Support.support_map]
  refine ⟨is,?_,Subtype.ext he.symm⟩
  exact (ConstructiveLists.all_support _ _).2 (fun i _ => ConstructiveBodyChoice.index_support 31 i)

#print axioms indices_call
#print axioms indices_complete
end properties.wasm_module_ok.ConstructiveBodyShuffle
