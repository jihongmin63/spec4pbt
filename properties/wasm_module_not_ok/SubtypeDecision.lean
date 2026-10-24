import properties.wasm_module_not_ok.StrtypeValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def supertypesValid (c : SpecTec.context)
    (hts : List SpecTec.heaptype) : Bool :=
  hts.all (properties.wasm_module_ok.HeaptypeValidation.heaptypeValid c)

theorem subtype_iter0_success_iff_valid (c : SpecTec.context)
    (hts : List SpecTec.heaptype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Subtype_ok:rule:iter:0» c hts⟩)
      start (.success (.of ())) finalSupply ↔
    supertypesValid c hts = true ∧ finalSupply = start := by
  induction hts generalizing start finalSupply with
  | nil =>
      constructor
      · intro h
        obtain ⟨_, hfinal⟩ :=
          SpecTecExecution.eval_deterministic program_primitive_deterministic h
            (subtype_iter0_nil_success c start)
        exact ⟨rfl, hfinal⟩
      · rintro ⟨_, rfl⟩
        exact subtype_iter0_nil_success c finalSupply
  | cons ht hts ih =>
      constructor
      · intro h
        obtain ⟨middle, hhead, htail⟩ :=
          (subtype_iter0_cons_success_iff c ht hts start finalSupply).1 h
        obtain ⟨hvalid, hmiddle⟩ :=
          (properties.wasm_module_ok.HeaptypeValidation.heaptype_success_iff_valid
            c ht start middle).1 hhead
        obtain ⟨hrest, hfinal⟩ := (ih middle finalSupply).1 htail
        constructor
        · simpa [supertypesValid, hvalid] using hrest
        · omega
      · rintro ⟨hall, rfl⟩
        have hsplit :
            properties.wasm_module_ok.HeaptypeValidation.heaptypeValid c ht = true ∧
              supertypesValid c hts = true := by
          simpa [supertypesValid] using hall
        have hhead :=
          (properties.wasm_module_ok.HeaptypeValidation.heaptype_success_iff_valid
            c ht finalSupply finalSupply).2 ⟨hsplit.1, rfl⟩
        have htail := (ih finalSupply finalSupply).2 ⟨hsplit.2, rfl⟩
        exact subtype_iter0_cons_success c ht hts
          finalSupply finalSupply finalSupply hhead htail

def subtypeValid (c : SpecTec.context) : SpecTec.subtype → Bool
  | .SubT _ hts strt =>
      decide (hts.length ≤ 1) && supertypesValid c hts && strtypeValid c strt

theorem subtype_ok_success_iff_valid (c : SpecTec.context)
    (st : SpecTec.subtype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Subtype_ok c st⟩)
      start (.success (.of ())) finalSupply ↔
    subtypeValid c st = true ∧ finalSupply = start := by
  cases st with
  | SubT fin hts strt =>
      constructor
      · intro h
        obtain ⟨hlen, middle, hiter, hstr⟩ :=
          (subtype_ok_success_iff c fin hts strt start finalSupply).1 h
        obtain ⟨hparents, hmiddle⟩ :=
          (subtype_iter0_success_iff_valid c hts start middle).1 hiter
        obtain ⟨hstrvalid, hfinal⟩ :=
          (strtype_ok_success_iff_valid c strt middle finalSupply).1 hstr
        constructor
        · simp [subtypeValid, hlen, hparents, hstrvalid]
        · omega
      · rintro ⟨hvalid, rfl⟩
        have hparts : (hts.length ≤ 1 ∧ supertypesValid c hts = true) ∧
            strtypeValid c strt = true := by
          simpa [subtypeValid, Bool.and_eq_true, decide_eq_true_eq] using hvalid
        have hiter :=
          (subtype_iter0_success_iff_valid c hts finalSupply finalSupply).2
            ⟨hparts.1.2, rfl⟩
        have hstr :=
          (strtype_ok_success_iff_valid c strt finalSupply finalSupply).2
            ⟨hparts.2, rfl⟩
        exact (subtype_ok_success_iff c fin hts strt
          finalSupply finalSupply).2
          ⟨hparts.1.1, finalSupply, hiter, hstr⟩

end properties.wasm_module_not_ok.Rejection
