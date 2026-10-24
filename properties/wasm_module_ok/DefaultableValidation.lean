import properties.wasm_module_ok.bundle.Helpers

set_option autoImplicit false

namespace properties.wasm_module_ok.DefaultableValidation

def defaultable : SpecTec.valtype → Bool
  | .NumT _ => true
  | .VecT _ => true
  | .RefT (.«% %» null _) => decide (null = .Null)
  | .BotT => false

theorem defaultable_total (t : SpecTec.valtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$defaultable» t⟩)
      n (.success (.of (defaultable t))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.«$defaultable_clauses» t) ())
    n (.success (.of (defaultable t))) n
  cases t with
  | NumT nt =>
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$defaultable:clause:0» (.NumT nt))
      n (.success (.of true)) n
    unfold SpecTec.«$defaultable:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · apply SpecTecExecution.Eval.guard_true
      rfl
    · exact SpecTecExecution.Eval.pure true
  | VecT vt =>
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$defaultable:clause:0» (.VecT vt)) n .unmatch n
      unfold SpecTec.«$defaultable:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      simp [SpecTec.«exec:match:valtype:NumT»]
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$defaultable:clause:1» (.VecT vt))
        n (.success (.of true)) n
      unfold SpecTec.«$defaultable:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · apply SpecTecExecution.Eval.guard_true
        rfl
      · exact SpecTecExecution.Eval.pure true
  | RefT rt =>
    cases rt with
    | «% %» null ht =>
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$defaultable:clause:0» (.RefT (.«% %» null ht)))
          n .unmatch n
        unfold SpecTec.«$defaultable:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        apply SpecTecExecution.Eval.guard_false
        simp [SpecTec.«exec:match:valtype:NumT»]
      · apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$defaultable:clause:1» (.RefT (.«% %» null ht)))
            n .unmatch n
          unfold SpecTec.«$defaultable:clause:1»
          apply SpecTecExecution.Eval.bind_unmatch
          apply SpecTecExecution.Eval.guard_false
          simp [SpecTec.«exec:match:valtype:VecT»]
        · apply SpecTecExecution.firstSuccess_cons_success
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$defaultable:clause:2» (.RefT (.«% %» null ht)))
            n (.success (.of (decide (null = .Null)))) n
          unfold SpecTec.«$defaultable:clause:2»
          apply SpecTecExecution.Eval.bind_success
          · apply SpecTecExecution.Eval.guard_true
            rfl
          · exact SpecTecExecution.Eval.pure (decide (null = .Null))
  | BotT =>
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$defaultable:clause:0» .BotT) n .unmatch n
      unfold SpecTec.«$defaultable:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      simp [SpecTec.«exec:match:valtype:NumT»]
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$defaultable:clause:1» .BotT) n .unmatch n
        unfold SpecTec.«$defaultable:clause:1»
        apply SpecTecExecution.Eval.bind_unmatch
        apply SpecTecExecution.Eval.guard_false
        simp [SpecTec.«exec:match:valtype:VecT»]
      · apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$defaultable:clause:2» .BotT) n .unmatch n
          unfold SpecTec.«$defaultable:clause:2»
          apply SpecTecExecution.Eval.bind_unmatch
          apply SpecTecExecution.Eval.guard_false
          simp [SpecTec.«exec:match:valtype:RefT»]
        · apply SpecTecExecution.firstSuccess_cons_success
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$defaultable:clause:3» .BotT)
            n (.success (.of false)) n
          unfold SpecTec.«$defaultable:clause:3»
          apply SpecTecExecution.Eval.bind_success
          · apply SpecTecExecution.Eval.guard_true
            rfl
          · exact SpecTecExecution.Eval.pure false

theorem defaultable_success_iff (t : SpecTec.valtype)
    (b : Bool) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$defaultable» t⟩)
      n (.success (.of b)) finalSupply ↔
      b = defaultable t ∧ finalSupply = n := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet h (defaultable_total t n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact defaultable_total t finalSupply

end properties.wasm_module_ok.DefaultableValidation
