import properties.wasm_module_ok.MemtypeValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.MemsValidation

def memDeclResult (c : SpecTec.context) (m : SpecTec.memory) :
    Option SpecTec.context :=
  if MemtypeValidation.memtypeValid m.MTYPE then
    some { c with MEMS := c.MEMS ++ [m.MTYPE] }
  else none

def memDeclOutcome (c : SpecTec.context) (m : SpecTec.memory) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match memDeclResult c m with
  | none => .unmatch
  | some result => .success (.of result)

theorem mem_ok_total (c : SpecTec.context)
    (m : SpecTec.memory) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Mem_ok c m⟩)
      n (memDeclOutcome c m) n := by
  cases hv : MemtypeValidation.memtypeValid m.MTYPE with
  | true =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.Mem_ok_clauses c m) ())
      n (memDeclOutcome c m) n
    simp only [memDeclOutcome, memDeclResult, hv, ite_true]
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Mem_ok:clause:0» c m)
      n (.success (.of { c with MEMS := c.MEMS ++ [m.MTYPE] })) n
    unfold SpecTec.«Mem_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact (MemtypeValidation.memtype_success_iff_valid
        c m.MTYPE n n).2 ⟨hv, rfl⟩
    · exact SpecTecExecution.Eval.pure
        { c with MEMS := c.MEMS ++ [m.MTYPE] }
  | false =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.Mem_ok_clauses c m) ())
      n (memDeclOutcome c m) n
    simp only [memDeclOutcome, memDeclResult, hv]
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Mem_ok:clause:0» c m) n .unmatch n
      unfold SpecTec.«Mem_ok:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      simpa [MemtypeValidation.memtypeOutcome, hv] using
        MemtypeValidation.memtype_total c m.MTYPE n
    · exact SpecTecExecution.firstSuccess_nil () n

theorem mem_ok_success_iff_result (c : SpecTec.context)
    (m : SpecTec.memory) (result : SpecTec.context)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Mem_ok c m⟩)
      n (.success (.of result)) finalSupply ↔
    memDeclResult c m = some result ∧ finalSupply = n := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet h (mem_ok_total c m n)
    cases hr : memDeclResult c m with
    | none => simp [memDeclOutcome, hr] at hout
    | some result' =>
      simp [memDeclOutcome, hr] at hout
      cases hout
      exact ⟨rfl, hsupply⟩
  · rintro ⟨hr, rfl⟩
    simpa [memDeclOutcome, hr] using mem_ok_total c m finalSupply

theorem mem_ok_none (c : SpecTec.context)
    (m : SpecTec.memory) (n : Nat)
    (hr : memDeclResult c m = none) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Mem_ok c m⟩)
      n .unmatch n := by
  simpa [memDeclOutcome, hr] using mem_ok_total c m n

def memsResult (c : SpecTec.context) :
    List SpecTec.memory → Option SpecTec.context
  | [] => some c
  | m :: ms =>
      (memDeclResult c m).bind fun c₁ => memsResult c₁ ms

def memsOutcome (c : SpecTec.context) (ms : List SpecTec.memory) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match memsResult c ms with
  | none => .unmatch
  | some result => .success (.of result)

theorem mems_total (c : SpecTec.context)
    (ms : List SpecTec.memory) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Mems_ok c ms⟩)
      n (memsOutcome c ms) n := by
  induction ms generalizing c with
  | nil =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.Mems_ok_clauses c []) ())
      n (memsOutcome c []) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Mems_ok:clause:0» c []) n .unmatch n
      unfold SpecTec.«Mems_ok:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      simp
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Mems_ok:clause:1» c [])
        n (memsOutcome c []) n
      unfold SpecTec.«Mems_ok:clause:1»
      simp only [memsOutcome, memsResult]
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · exact SpecTecExecution.Eval.pure c
  | cons m ms ih =>
    cases hhead : memDeclResult c m with
    | none =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.Mems_ok_clauses c (m :: ms)) ())
        n (memsOutcome c (m :: ms)) n
      simp only [memsOutcome, memsResult, hhead, Option.bind_none]
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«Mems_ok:clause:0» c (m :: ms)) n .unmatch n
        unfold SpecTec.«Mems_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · apply SpecTecExecution.Eval.bind_unmatch
          exact mem_ok_none c m n hhead
      · apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«Mems_ok:clause:1» c (m :: ms)) n .unmatch n
          unfold SpecTec.«Mems_ok:clause:1»
          apply SpecTecExecution.Eval.bind_unmatch
          apply SpecTecExecution.Eval.guard_false
          simp
        · exact SpecTecExecution.firstSuccess_nil () n
    | some c₁ =>
      cases htail : memsResult c₁ ms with
      | none =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.Mems_ok_clauses c (m :: ms)) ())
          n (memsOutcome c (m :: ms)) n
        simp only [memsOutcome, memsResult, hhead,
          Option.bind_some, htail]
        apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«Mems_ok:clause:0» c (m :: ms)) n .unmatch n
          unfold SpecTec.«Mems_ok:clause:0»
          apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true rfl
          · apply SpecTecExecution.Eval.bind_success
            · exact (mem_ok_success_iff_result c m c₁ n n).2 ⟨hhead, rfl⟩
            · apply SpecTecExecution.Eval.bind_unmatch
              simpa [memsOutcome, htail] using ih c₁
        · apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«Mems_ok:clause:1» c (m :: ms)) n .unmatch n
            unfold SpecTec.«Mems_ok:clause:1»
            apply SpecTecExecution.Eval.bind_unmatch
            apply SpecTecExecution.Eval.guard_false
            simp
          · exact SpecTecExecution.firstSuccess_nil () n
      | some result =>
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.Mems_ok_clauses c (m :: ms)) ())
          n (memsOutcome c (m :: ms)) n
        simp only [memsOutcome, memsResult, hhead,
          Option.bind_some, htail]
        apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«Mems_ok:clause:0» c (m :: ms))
          n (.success (.of result)) n
        unfold SpecTec.«Mems_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · apply SpecTecExecution.Eval.bind_success
          · exact (mem_ok_success_iff_result c m c₁ n n).2 ⟨hhead, rfl⟩
          · apply SpecTecExecution.Eval.bind_success
            · simpa [memsOutcome, htail] using ih c₁
            · exact SpecTecExecution.Eval.pure result

theorem mems_success_iff_result (c : SpecTec.context)
    (ms : List SpecTec.memory) (result : SpecTec.context)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Mems_ok c ms⟩)
      n (.success (.of result)) finalSupply ↔
    memsResult c ms = some result ∧ finalSupply = n := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet h (mems_total c ms n)
    cases hr : memsResult c ms with
    | none => simp [memsOutcome, hr] at hout
    | some result' =>
      simp [memsOutcome, hr] at hout
      cases hout
      exact ⟨rfl, hsupply⟩
  · rintro ⟨hr, rfl⟩
    simpa [memsOutcome, hr] using mems_total c ms finalSupply

theorem mems_none (c : SpecTec.context)
    (ms : List SpecTec.memory) (n : Nat)
    (hr : memsResult c ms = none) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Mems_ok c ms⟩)
      n .unmatch n := by
  simpa [memsOutcome, hr] using mems_total c ms n

end properties.wasm_module_ok.MemsValidation
