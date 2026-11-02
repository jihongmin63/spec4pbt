import properties.wasm_module_ok.SubstOutputHeaptypeList

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstOutputValtypes

open properties.wasm_module_not_ok.Rejection

theorem substReftypeResult_output_fixed
    (rt : SpecTec.reftype) (pref dts : List SpecTec.deftype)
    (result : SpecTec.reftype)
    (h : substReftypeResult rt pref = some result) :
    substReftypeResult result dts = some result := by
  cases rt with
  | «% %» null ht =>
      cases hh : substHeaptypeResult ht pref with
      | none => simp [substReftypeResult, hh] at h
      | some ht' =>
          have hr : result = SpecTec.reftype.«% %» null ht' := by
            simpa [substReftypeResult, hh] using h.symm
          subst result
          simp [substReftypeResult,
            SubstOutputHeaptype.substHeaptypeResult_output_fixed
              ht pref dts ht' hh]

theorem substValtypeResult_output_fixed
    (t : SpecTec.valtype) (pref dts : List SpecTec.deftype)
    (result : SpecTec.valtype)
    (h : substValtypeResult t pref = some result) :
    substValtypeResult result dts = some result := by
  cases t with
  | RefT rt =>
      cases hr : substReftypeResult rt pref with
      | none => simp [substValtypeResult, hr] at h
      | some rt' =>
          have hresult : result = SpecTec.valtype.RefT rt' := by
            simpa [substValtypeResult, hr] using h.symm
          subst result
          simp [substValtypeResult,
            substReftypeResult_output_fixed rt pref dts rt' hr]
  | NumT nt =>
      have hr : result = .NumT nt := by
        simpa [substValtypeResult] using h.symm
      subst result
      rfl
  | VecT vt =>
      have hr : result = .VecT vt := by
        simpa [substValtypeResult] using h.symm
      subst result
      rfl
  | BotT =>
      have hr : result = .BotT := by
        simpa [substValtypeResult] using h.symm
      subst result
      rfl

theorem substResulttypeResult_output_fixed
    (ts : List SpecTec.valtype) (pref dts : List SpecTec.deftype)
    (result : List SpecTec.valtype)
    (h : substResulttypeResult ts pref = some result) :
    substResulttypeResult result dts = some result := by
  induction ts generalizing result with
  | nil =>
      have hr : result = [] := by
        simpa [substResulttypeResult] using h.symm
      subst result
      rfl
  | cons t ts ih =>
      cases hhead : substValtypeResult t pref with
      | none => simp [substResulttypeResult, hhead] at h
      | some t' =>
          cases hrest : substResulttypeResult ts pref with
          | none => simp [substResulttypeResult, hhead, hrest] at h
          | some ts' =>
              have hr : result = t' :: ts' := by
                simpa [substResulttypeResult, hhead, hrest] using h.symm
              subst result
              simp [substResulttypeResult,
                substValtypeResult_output_fixed t pref dts t' hhead,
                ih ts' hrest]

end properties.wasm_module_ok.SubstOutputValtypes
