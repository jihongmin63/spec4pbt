import properties.wasm_module_ok.ConstructiveBodyReferenceBranchCalls
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyValidReferences
open SpecTec properties.wasm_module_ok

structure Ref (c : context) where
  value : reftype
  valid : ValtypeValidation.valtypeValid c (.RefT value)=true

def all (c : context) : List (Ref c) :=
  (FiniteValidTypes.heapCandidates c).attach.flatMap fun (heap : {h : heaptype // h∈FiniteValidTypes.heapCandidates c}) =>
    [⟨.«% %» .Null heap.val,(FiniteValidTypes.heapCandidates_spec c heap.val).1 heap.property⟩,
     ⟨.«% %» .NoNull heap.val,(FiniteValidTypes.heapCandidates_spec c heap.val).1 heap.property⟩]

theorem complete (c : context) (r : Ref c) : r∈all c := by
  cases r with | mk rt hv =>
   cases rt with | «% %» nu heap =>
    have hh := (FiniteValidTypes.heapCandidates_spec c heap).2 hv
    apply List.mem_flatMap.mpr
    refine ⟨⟨heap,hh⟩,by simp,?_⟩
    cases nu <;> simp

theorem Ref.backed {c : context} (r : Ref c) : CandidateValMatch.InTableVal c (.RefT r.value) :=
  CandidateValMembership.valid_candidate_in_table c _ ((FiniteValidTypes.validCandidates_spec c _).2 r.valid)

theorem Ref.call {c : context} (r : Ref c) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Reftype_ok c r.value⟩) n (.success (.of ())) n := by
  cases r with | mk rt hv =>
   cases rt with | «% %» nu heap =>
    exact (ValtypeValidation.reftype_success_iff c nu heap n n).2
      ((HeaptypeValidation.heaptype_success_iff_valid c heap n n).2 ⟨hv,rfl⟩)

#print axioms complete
end properties.wasm_module_ok.ConstructiveBodyValidReferences
