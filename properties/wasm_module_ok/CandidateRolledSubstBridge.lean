import properties.wasm_module_ok.CandidateSubstList
import properties.wasm_module_ok.CandidateRectypeTable

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateRolledSubstBridge

open properties.wasm_module_not_ok.Rejection

theorem rolledDefs_range'
    (rect : SpecTec.rectype) (i count : Nat) :
    rolledDefs rect i count =
      (List.range' i count).map (fun j => SpecTec.deftype.DefT rect j) := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih => simp [rolledDefs, List.range', ih]

theorem subst_rolledDefs_some
    (c : SpecTec.context) (rect rect' : SpecTec.rectype)
    (i count : Nat)
    (hrect : substRectypeResult rect c.TYPES = some rect') :
    CandidateSubstList.substList c (rolledDefs rect i count) =
      some (rolledDefs rect' i count) := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
      simp [rolledDefs, CandidateSubstList.substList,
        substDeftypeResult, hrect, ih]

theorem subst_rolledDefs_none
    (c : SpecTec.context) (rect : SpecTec.rectype)
    (i count : Nat)
    (hrect : substRectypeResult rect c.TYPES = none) :
    CandidateSubstList.substList c (rolledDefs rect i (count + 1)) = none := by
  simp [rolledDefs, CandidateSubstList.substList,
    substDeftypeResult, hrect]

theorem subst_rolled_exact
    (c : SpecTec.context) (sts : List SpecTec.subtype) :
    CandidateSubstList.substList c
        (rollDeftypes c.TYPES.length (.RecT sts)) =
      (CandidateRectypeTable.transformed c sts).map fun rect' =>
        (List.range sts.length).map fun i => SpecTec.deftype.DefT rect' i := by
  let rect : SpecTec.rectype :=
    .RecT (rollSubtypes sts c.TYPES.length
      (sts.length + c.TYPES.length))
  have hrolled : rollDeftypes c.TYPES.length (.RecT sts) =
      rolledDefs rect 0 sts.length := by
    simp [rollDeftypes, rollRectypeAt, rollRectype, rect, rollSubtypes]
  have htrans : CandidateRectypeTable.transformed c sts =
      substRectypeResult rect c.TYPES := rfl
  rw [hrolled, htrans]
  cases sts with
  | nil =>
      simp [rect, rollSubtypes, rolledDefs,
        CandidateSubstList.substList, substRectypeResult,
        substSubtypeListResult]
  | cons st rest =>
      cases hresult : substRectypeResult rect c.TYPES with
      | none =>
          simp [subst_rolledDefs_none c rect 0 rest.length hresult]
      | some rect' =>
          rw [subst_rolledDefs_some c rect rect' 0 (st :: rest).length hresult]
          simp [rolledDefs_range', List.range_eq_range']

end properties.wasm_module_ok.CandidateRolledSubstBridge
