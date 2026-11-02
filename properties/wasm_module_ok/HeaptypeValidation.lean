import properties.wasm_module_ok.bundle.Helpers

set_option autoImplicit false

namespace properties.wasm_module_ok.HeaptypeValidation

def baseHeaptypes : List SpecTec.heaptype :=
  [.AnyHT, .NoneHT, .EqHT, .I31HT, .StructHT, .ArrayHT,
   .FuncHT, .NoFuncHT, .ExnHT, .NoExnHT, .ExternHT,
   .NoExternHT, .BotHT]

def heaptypeValid (c : SpecTec.context) (ht : SpecTec.heaptype) : Bool :=
  match ht with
  | .VarHT (.StatX x) => decide (x < c.TYPES.length)
  | .VarHT (.RecX _) => false
  | .DefHT _ => false
  | _ => true

theorem heaptype_valid_iff (c : SpecTec.context)
    (ht : SpecTec.heaptype) :
    heaptypeValid c ht = true ↔
      ht ∈ baseHeaptypes ∨
        ∃ x : Nat, ht = .VarHT (.StatX x) ∧ x < c.TYPES.length := by
  cases ht <;> simp [heaptypeValid, baseHeaptypes]
  case VarHT tv =>
    cases tv <;> simp [heaptypeValid, baseHeaptypes]

theorem heaptype_base_success (c : SpecTec.context)
    (ht : SpecTec.heaptype) (n : Nat)
    (hbase : ht ∈ baseHeaptypes) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Heaptype_ok c ht⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Heaptype_ok_clauses c ht))
    n (.success (.of ())) n
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Heaptype_ok:clause:0» c ht)
    n (.success (.of ())) n
  unfold SpecTec.«Heaptype_ok:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · apply SpecTecExecution.Eval.guard_true
    simpa [baseHeaptypes] using hbase
  · exact SpecTecExecution.Eval.pure ()

theorem heaptype_stat_success (c : SpecTec.context)
    (x n : Nat) (hbound : x < c.TYPES.length) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Heaptype_ok
        c (.VarHT (.StatX x))⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.Heaptype_ok_clauses c (.VarHT (.StatX x))))
    n (.success (.of ())) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Heaptype_ok:clause:0» c (.VarHT (.StatX x)))
      n .unmatch n
    unfold SpecTec.«Heaptype_ok:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    apply SpecTecExecution.Eval.guard_false
    simp
  · apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Heaptype_ok:clause:1» c (.VarHT (.StatX x)))
      n (.success (.of ())) n
    unfold SpecTec.«Heaptype_ok:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · apply SpecTecExecution.Eval.guard_true
      rfl
    · apply SpecTecExecution.Eval.bind_success
      · apply SpecTecExecution.Eval.guard_true
        rfl
      · apply SpecTecExecution.Eval.bind_success
        · apply SpecTecExecution.Eval.guard_true
          exact ⟨Nat.zero_le x, hbound⟩
        · exact SpecTecExecution.Eval.pure ()

theorem heaptype_success_iff (c : SpecTec.context)
    (ht : SpecTec.heaptype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Heaptype_ok c ht⟩)
      n (.success (.of ())) finalSupply ↔
    (ht ∈ baseHeaptypes ∨
      ∃ x : Nat, ht = .VarHT (.StatX x) ∧ x < c.TYPES.length) ∧
    finalSupply = n := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«Heaptype_ok:clause:0» c ht)
          (fun _ => SpecTecExecution.tryClauses
            [fun _ => SpecTec.«Heaptype_ok:clause:1» c ht]))
        n (.success (.of ())) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        unfold SpecTec.«Heaptype_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hguard hpure =>
          cases hguard with
          | guard_true hbase =>
            cases hpure with
            | pure => exact ⟨Or.inl (by simpa [baseHeaptypes] using hbase), rfl⟩
      | orElse_unmatch _ htail =>
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Heaptype_ok:clause:1» c ht)
            (fun _ => .unmatch))
          n (.success (.of ())) finalSupply at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Heaptype_ok:clause:1» at hsecond
          cases hsecond with
          | bind_success hsub htail =>
            cases hsub with
            | guard_true hsub_true =>
              cases ht <;>
                simp [SpecTec.«sub:heaptype:heaptypeVar»] at hsub_true
              case VarHT _ _ a _ =>
                cases a with
                | RecX x =>
                  cases htail with
                  | bind_success hstat _ =>
                    cases hstat with
                    | guard_true hcond =>
                      simp [SpecTec.«exec:match:typevar:StatX»] at hcond
                | StatX x =>
                  cases htail with
                  | bind_success hstat htail =>
                    cases hstat with
                    | guard_true _ =>
                      cases htail with
                      | bind_success hbound hpure =>
                        cases hbound with
                        | guard_true hbounds =>
                          cases hpure with
                          | pure => exact ⟨Or.inr ⟨x, rfl, hbounds.2⟩, rfl⟩
        | orElse_unmatch _ hnone => cases hnone
  · rintro ⟨hvalid, rfl⟩
    cases hvalid with
    | inl hbase => exact heaptype_base_success c ht finalSupply hbase
    | inr hstat =>
      obtain ⟨x, hshape, hbound⟩ := hstat
      subst ht
      exact heaptype_stat_success c x finalSupply hbound

theorem heaptype_success_iff_valid (c : SpecTec.context)
    (ht : SpecTec.heaptype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Heaptype_ok c ht⟩)
      n (.success (.of ())) finalSupply ↔
    heaptypeValid c ht = true ∧ finalSupply = n := by
  rw [heaptype_success_iff, heaptype_valid_iff]

end properties.wasm_module_ok.HeaptypeValidation
