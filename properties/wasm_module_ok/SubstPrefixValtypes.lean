import properties.wasm_module_ok.SubstPrefixReftype

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstPrefixValtypes

open properties.wasm_module_not_ok.Rejection

theorem substValtypeResult_prefix
    (t : SpecTec.valtype)
    (pref tail : List SpecTec.deftype)
    (result : SpecTec.valtype)
    (h : substValtypeResult t pref = some result) :
    substValtypeResult t (pref ++ tail) = some result := by
  cases t with
  | RefT rt =>
      cases hrt : substReftypeResult rt pref with
      | none =>
          simp [substValtypeResult, hrt] at h
      | some rt' =>
          have hr : result = SpecTec.valtype.RefT rt' := by
            simpa [substValtypeResult, hrt] using h.symm
          subst result
          simp [substValtypeResult,
            SubstPrefixReftype.substReftypeResult_prefix rt pref tail rt' hrt]
  | NumT nt => simpa [substValtypeResult] using h
  | VecT vt => simpa [substValtypeResult] using h
  | BotT => simpa [substValtypeResult] using h

theorem substResulttypeResult_prefix
    (ts : List SpecTec.valtype)
    (pref tail : List SpecTec.deftype)
    (result : List SpecTec.valtype)
    (h : substResulttypeResult ts pref = some result) :
    substResulttypeResult ts (pref ++ tail) = some result := by
  induction ts generalizing result with
  | nil =>
      simpa [substResulttypeResult] using h
  | cons t ts ih =>
      cases hhead : substValtypeResult t pref with
      | none =>
          simp [substResulttypeResult, hhead] at h
      | some t' =>
          cases hrest : substResulttypeResult ts pref with
          | none =>
              simp [substResulttypeResult, hhead, hrest] at h
          | some ts' =>
              have hr : result = t' :: ts' := by
                simpa [substResulttypeResult, hhead, hrest] using h.symm
              subst result
              simp [substResulttypeResult,
                substValtypeResult_prefix t pref tail t' hhead,
                ih ts' hrest]

end properties.wasm_module_ok.SubstPrefixValtypes
