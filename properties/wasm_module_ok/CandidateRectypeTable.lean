import properties.wasm_module_ok.CandidateTypeReadySuccess
import properties.wasm_module_ok.RectypeAppendedShape
import properties.wasm_module_ok.RectypeLengthValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateRectypeTable

open properties.wasm_module_not_ok.Rejection

/-- The group-wide substitution is computed before any recursive type match. -/
def transformed (c : SpecTec.context) (sts : List SpecTec.subtype) :
    Option SpecTec.rectype :=
  substRectypeResult
    (.RecT (rollSubtypes sts c.TYPES.length
      (sts.length + c.TYPES.length))) c.TYPES

/-- The type table installed by the non-matching prefix of `Rectype_ok`. -/
def candidateContext (c : SpecTec.context)
    (sts : List SpecTec.subtype) : Option SpecTec.context :=
  (transformed c sts).map fun rect' =>
    { c with TYPES := c.TYPES ++
      (List.range sts.length).map (fun i => .DefT rect' i) }

/-- A successful recursive-group call has exactly the computed candidate table. -/
theorem rectype_success_candidateContext
    (c result : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of result)) finish) :
    candidateContext c sts = some result := by
  obtain ⟨dts, hresult, hposition⟩ :=
    RectypeAppendedShape.rectype_ok_appended_position_shape
      c result sts start finish hrect
  obtain ⟨dts', hresult', hlength'⟩ :=
    RectypeLengthValidation.rectype_ok_appended_types_length
      c result sts start finish hrect
  have hlen : dts.length = sts.length := by
    have heq : c.TYPES ++ dts = c.TYPES ++ dts' :=
      congrArg SpecTec.context.TYPES (hresult.symm.trans hresult')
    exact (congrArg List.length (List.append_cancel_left heq)).trans hlength'
  cases sts with
  | nil =>
      have hdts : dts = [] := List.length_eq_zero_iff.mp hlen
      subst dts
      simpa [candidateContext, transformed, rollSubtypes,
        substRectypeResult, substSubtypeListResult] using hresult.symm
  | cons hd tl =>
      have hzero : 0 < (hd :: tl).length := by simp
      obtain ⟨rect', hget0, htrans⟩ := hposition 0 hzero
      have htable : dts =
          (List.range (hd :: tl).length).map (fun i => .DefT rect' i) := by
        apply List.ext_getElem
        · simpa using hlen
        · intro i hi₁ hi₂
          obtain ⟨rectI, hgetI, htransI⟩ := hposition i (hlen ▸ hi₁)
          have heq : rectI = rect' :=
            Option.some.inj (htransI.symm.trans htrans)
          subst rectI
          have hleft : dts[i]? = some dts[i] :=
            List.getElem?_eq_getElem hi₁
          rw [hgetI] at hleft
          have hvalue : dts[i] = SpecTec.deftype.DefT rect' i :=
            Option.some.inj hleft.symm
          simpa using hvalue
      rw [htable] at hresult
      change transformed c (hd :: tl) = some rect' at htrans
      unfold candidateContext
      rw [htrans]
      exact congrArg some hresult.symm

/-- The pre-match finite readiness check accepts every successful group. -/
theorem rectype_success_candidate_ready
    (c result : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of result)) finish) :
    ∃ candidate,
      candidateContext c sts = some candidate ∧
      CandidateTypeReadyDecide.tableReady candidate = true := by
  exact ⟨result,
    rectype_success_candidateContext c result sts start finish hrect,
    CandidateTypeReadySuccess.rectype_success_tableReady
      c result sts start finish hc hrect⟩

end properties.wasm_module_ok.CandidateRectypeTable
