import properties.wasm_module_ok.CandidateSupertypeIter
import properties.wasm_module_ok.SubtypeStaticMatchTrace
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateStaticSuperCheck

/-- Finite exact check for one static supertype in the closing pass. -/
def staticSuperCheck (c : SpecTec.context) (x : SpecTec.typeidx)
    (strt : SpecTec.strtype) : SpecTec.heaptype → Bool
  | .VarHT (.StatX y) =>
      match c.TYPES[y]? with
      | none => false
      | some dt => ReadyStaticSubtypeMatch.staticSuperMatch c x y strt dt
  | _ => false

theorem static_super_check_success_iff
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (sourceFin : SpecTec.final) (sourceHts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (ht : SpecTec.heaptype)
    (subStart subFinish n finish : Nat)
    (hsub : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Subtype_ok c
          (.SubT sourceFin sourceHts strt)⟩)
      subStart (.success (.of ())) subFinish)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (hready : CandidateTypeReady.Ready c) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Subtype_sub_ok' c x strt ht⟩)
      n (.success (.of ())) finish ↔
    staticSuperCheck c x strt ht = true ∧ finish = n := by
  constructor
  · intro hcall
    obtain ⟨y, hshape, _⟩ :=
      SubtypeSupertypeShape.subtype_sub_ok_prime_shape
        c x strt ht n finish hcall
    subst ht
    obtain ⟨dt, fin, hts, strtU, middle,
      hlookup, hunroll, hmatch, hlt, hfinal⟩ :=
      SubtypeStaticMatchTrace.subtype_sub_ok_static_match_trace
        c x y strt n finish hcall
    have hresult :=
      ReadyStaticSubtypeMatch.static_subtype_sub_ok_result_of_ready
        c x y sourceFin sourceHts strt dt
        subStart subFinish n hsub hnested hready hlookup
    by_cases hbool :
        ReadyStaticSubtypeMatch.staticSuperMatch c x y strt dt = true
    · rw [if_pos hbool] at hresult
      obtain ⟨_, hsupply⟩ :=
        properties.wasm_module_ok.Execution.eval_deterministic hcall hresult
      exact ⟨by simp [staticSuperCheck, hlookup, hbool], hsupply⟩
    · rw [if_neg hbool] at hresult
      obtain ⟨hout, _⟩ :=
        properties.wasm_module_ok.Execution.eval_deterministic hcall hresult
      cases hout
  · rintro ⟨hcheck, rfl⟩
    cases ht <;> simp [staticSuperCheck] at hcheck
    case VarHT tv =>
      cases tv <;> simp at hcheck
      case StatX y =>
        cases hlookup : c.TYPES[y]? with
        | none => simp [hlookup] at hcheck
        | some dt =>
            have hbool :
                ReadyStaticSubtypeMatch.staticSuperMatch c x y strt dt = true := by
              simpa [hlookup] using hcheck
            have hresult :=
              ReadyStaticSubtypeMatch.static_subtype_sub_ok_result_of_ready
                c x y sourceFin sourceHts strt dt
                subStart subFinish finish hsub hnested hready hlookup
            rwa [if_pos hbool] at hresult

end properties.wasm_module_ok.CandidateStaticSuperCheck
