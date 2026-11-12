import properties.wasm_module_ok.SubstPrefixDeftype

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstPrefixCall

open properties.wasm_module_not_ok.Rejection

theorem subst_deftype_call_prefix
    (dt : SpecTec.deftype) (pref tail : List SpecTec.deftype)
    (result : SpecTec.deftype) (start : Nat)
    (h : substDeftypeResult dt pref = some result) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.deftype,
        SpecTec.Call.«$subst_deftype» (List SpecTec.deftype)
          (pref ++ tail) SpecTec.Call.«$subst_of» dt⟩)
      start (.success (.of result)) start := by
  have hext := SubstPrefixDeftype.substDeftypeResult_prefix
    dt pref tail result h
  simpa [optionOutcome, hext] using
    subst_deftype_of_total dt (pref ++ tail) start

end properties.wasm_module_ok.SubstPrefixCall
