import properties.wasm_module_ok.SubstPrefixFields

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstPrefixStrtype

open properties.wasm_module_not_ok.Rejection

theorem substStructtypeResult_prefix
    (st : SpecTec.structtype) (pref tail : List SpecTec.deftype)
    (result : SpecTec.structtype)
    (h : substStructtypeResult st pref = some result) :
    substStructtypeResult st (pref ++ tail) = some result := by
  cases st with
  | StructT fields =>
      cases hf : substFieldtypeListResult fields pref with
      | none => simp [substStructtypeResult, hf] at h
      | some fields' =>
          have hr : result = SpecTec.structtype.StructT fields' := by
            simpa [substStructtypeResult, hf] using h.symm
          subst result
          simp [substStructtypeResult,
            SubstPrefixFields.substFieldtypeListResult_prefix
              fields pref tail fields' hf]

theorem substArraytypeResult_prefix
    (arrType : SpecTec.arraytype) (pref tail : List SpecTec.deftype)
    (result : SpecTec.arraytype)
    (h : substArraytypeResult arrType pref = some result) :
    substArraytypeResult arrType (pref ++ tail) = some result := by
  cases arrType with
  | ArrayT field =>
      cases hf : substFieldtypeResult field pref with
      | none => simp [substArraytypeResult, hf] at h
      | some field' =>
          have hr : result = SpecTec.arraytype.ArrayT field' := by
            simpa [substArraytypeResult, hf] using h.symm
          subst result
          simp [substArraytypeResult,
            SubstPrefixFields.substFieldtypeResult_prefix
              field pref tail field' hf]

theorem substFunctypeResult_prefix
    (ft : SpecTec.functype) (pref tail : List SpecTec.deftype)
    (result : SpecTec.functype)
    (h : substFunctypeResult ft pref = some result) :
    substFunctypeResult ft (pref ++ tail) = some result := by
  cases ft with
  | FuncT ins outs =>
      cases hi : substResulttypeResult ins pref with
      | none => simp [substFunctypeResult, hi] at h
      | some ins' =>
          cases ho : substResulttypeResult outs pref with
          | none => simp [substFunctypeResult, hi, ho] at h
          | some outs' =>
              have hr : result = SpecTec.functype.FuncT ins' outs' := by
                simpa [substFunctypeResult, hi, ho] using h.symm
              subst result
              simp [substFunctypeResult,
                SubstPrefixValtypes.substResulttypeResult_prefix
                  ins pref tail ins' hi,
                SubstPrefixValtypes.substResulttypeResult_prefix
                  outs pref tail outs' ho]

theorem substStrtypeResult_prefix
    (st : SpecTec.strtype) (pref tail : List SpecTec.deftype)
    (result : SpecTec.strtype)
    (h : substStrtypeResult st pref = some result) :
    substStrtypeResult st (pref ++ tail) = some result := by
  cases st with
  | DefStructT struct =>
      cases hs : substStructtypeResult struct pref with
      | none => simp [substStrtypeResult, hs] at h
      | some struct' =>
          have hr : result = SpecTec.strtype.DefStructT struct' := by
            simpa [substStrtypeResult, hs] using h.symm
          subst result
          simp [substStrtypeResult,
            substStructtypeResult_prefix struct pref tail struct' hs]
  | DefArrayT arr =>
      cases ha : substArraytypeResult arr pref with
      | none => simp [substStrtypeResult, ha] at h
      | some arr' =>
          have hr : result = SpecTec.strtype.DefArrayT arr' := by
            simpa [substStrtypeResult, ha] using h.symm
          subst result
          simp [substStrtypeResult,
            substArraytypeResult_prefix arr pref tail arr' ha]
  | DefFuncT ft =>
      cases hf : substFunctypeResult ft pref with
      | none => simp [substStrtypeResult, hf] at h
      | some ft' =>
          have hr : result = SpecTec.strtype.DefFuncT ft' := by
            simpa [substStrtypeResult, hf] using h.symm
          subst result
          simp [substStrtypeResult,
            substFunctypeResult_prefix ft pref tail ft' hf]

end properties.wasm_module_ok.SubstPrefixStrtype
