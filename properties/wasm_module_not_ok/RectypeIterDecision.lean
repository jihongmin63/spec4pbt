import properties.wasm_module_not_ok.SubtypeDecision

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def subtypesValid (c : SpecTec.context)
    (sts : List SpecTec.subtype) : Bool :=
  sts.all (subtypeValid c)

theorem rectype_iter5_success_iff_valid (c : SpecTec.context)
    (sts : List SpecTec.subtype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:5» c sts⟩)
      start (.success (.of ())) finalSupply ↔
    subtypesValid c sts = true ∧ finalSupply = start := by
  induction sts generalizing start finalSupply with
  | nil =>
      constructor
      · intro h
        obtain ⟨_, hfinal⟩ :=
          SpecTecExecution.eval_deterministic program_primitive_deterministic h
            (rectype_iter5_nil_success c start)
        exact ⟨rfl, hfinal⟩
      · rintro ⟨_, rfl⟩
        exact rectype_iter5_nil_success c finalSupply
  | cons st sts ih =>
      constructor
      · intro h
        obtain ⟨middle, hhead, htail⟩ :=
          (rectype_iter5_cons_success_iff c st sts start finalSupply).1 h
        obtain ⟨hvalid, hmiddle⟩ :=
          (subtype_ok_success_iff_valid c st start middle).1 hhead
        obtain ⟨hrest, hfinal⟩ := (ih middle finalSupply).1 htail
        constructor
        · simpa [subtypesValid, hvalid] using hrest
        · omega
      · rintro ⟨hall, rfl⟩
        have hsplit : subtypeValid c st = true ∧
            subtypesValid c sts = true := by
          simpa [subtypesValid] using hall
        have hhead :=
          (subtype_ok_success_iff_valid c st finalSupply finalSupply).2
            ⟨hsplit.1, rfl⟩
        have htail := (ih finalSupply finalSupply).2 ⟨hsplit.2, rfl⟩
        exact rectype_iter5_cons_success c st sts
          finalSupply finalSupply finalSupply hhead htail

end properties.wasm_module_not_ok.Rejection
