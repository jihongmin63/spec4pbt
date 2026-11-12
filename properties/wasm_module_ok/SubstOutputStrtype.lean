import properties.wasm_module_ok.SubstOutputFields

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstOutputStrtype

open properties.wasm_module_not_ok.Rejection

theorem substStructtypeResult_output_fixed
    (st : SpecTec.structtype) (pref dts : List SpecTec.deftype)
    (result : SpecTec.structtype)
    (h : substStructtypeResult st pref = some result) :
    substStructtypeResult result dts = some result := by
  cases st with
  | StructT fields =>
      cases hf : substFieldtypeListResult fields pref with
      | none => simp [substStructtypeResult, hf] at h
      | some fields' =>
          have hr : result = SpecTec.structtype.StructT fields' := by
            simpa [substStructtypeResult, hf] using h.symm
          subst result
          simp [substStructtypeResult,
            SubstOutputFields.substFieldtypeListResult_output_fixed
              fields pref dts fields' hf]

theorem substArraytypeResult_output_fixed
    (arr : SpecTec.arraytype) (pref dts : List SpecTec.deftype)
    (result : SpecTec.arraytype)
    (h : substArraytypeResult arr pref = some result) :
    substArraytypeResult result dts = some result := by
  cases arr with
  | ArrayT field =>
      cases hf : substFieldtypeResult field pref with
      | none => simp [substArraytypeResult, hf] at h
      | some field' =>
          have hr : result = SpecTec.arraytype.ArrayT field' := by
            simpa [substArraytypeResult, hf] using h.symm
          subst result
          simp [substArraytypeResult,
            SubstOutputFields.substFieldtypeResult_output_fixed
              field pref dts field' hf]

theorem substFunctypeResult_output_fixed
    (ft : SpecTec.functype) (pref dts : List SpecTec.deftype)
    (result : SpecTec.functype)
    (h : substFunctypeResult ft pref = some result) :
    substFunctypeResult result dts = some result := by
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
                SubstOutputValtypes.substResulttypeResult_output_fixed
                  ins pref dts ins' hi,
                SubstOutputValtypes.substResulttypeResult_output_fixed
                  outs pref dts outs' ho]

theorem substStrtypeResult_output_fixed
    (st : SpecTec.strtype) (pref dts : List SpecTec.deftype)
    (result : SpecTec.strtype)
    (h : substStrtypeResult st pref = some result) :
    substStrtypeResult result dts = some result := by
  cases st with
  | DefStructT struct =>
      cases hs : substStructtypeResult struct pref with
      | none => simp [substStrtypeResult, hs] at h
      | some struct' =>
          have hr : result = SpecTec.strtype.DefStructT struct' := by
            simpa [substStrtypeResult, hs] using h.symm
          subst result
          simp [substStrtypeResult,
            substStructtypeResult_output_fixed struct pref dts struct' hs]
  | DefArrayT arr =>
      cases ha : substArraytypeResult arr pref with
      | none => simp [substStrtypeResult, ha] at h
      | some arr' =>
          have hr : result = SpecTec.strtype.DefArrayT arr' := by
            simpa [substStrtypeResult, ha] using h.symm
          subst result
          simp [substStrtypeResult,
            substArraytypeResult_output_fixed arr pref dts arr' ha]
  | DefFuncT ft =>
      cases hf : substFunctypeResult ft pref with
      | none => simp [substStrtypeResult, hf] at h
      | some ft' =>
          have hr : result = SpecTec.strtype.DefFuncT ft' := by
            simpa [substStrtypeResult, hf] using h.symm
          subst result
          simp [substStrtypeResult,
            substFunctypeResult_output_fixed ft pref dts ft' hf]

end properties.wasm_module_ok.SubstOutputStrtype
