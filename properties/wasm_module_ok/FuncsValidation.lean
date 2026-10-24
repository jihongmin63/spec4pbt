import properties.wasm_module_ok.FuncDeclValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.FuncsValidation

def funcsResult (c : SpecTec.context) :
    List SpecTec.func → Option SpecTec.context
  | [] => some c
  | f :: fs =>
      (FuncDeclValidation.funcDeclResult c f).bind fun c₁ =>
        funcsResult c₁ fs

theorem funcs_nil_total (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Funcs_ok c []⟩)
      n (.success (.of c)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.Funcs_ok_clauses c []) ())
    n (.success (.of c)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Funcs_ok:clause:0» c []) n .unmatch n
    unfold SpecTec.«Funcs_ok:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    apply SpecTecExecution.Eval.guard_false
    simp
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Funcs_ok:clause:1» c [])
      n (.success (.of c)) n
    unfold SpecTec.«Funcs_ok:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · apply SpecTecExecution.Eval.guard_true
      rfl
    · exact SpecTecExecution.Eval.pure c

theorem funcs_cons_success_iff (c : SpecTec.context)
    (f : SpecTec.func) (fs : List SpecTec.func)
    (result : SpecTec.context) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Funcs_ok c (f :: fs)⟩)
      n (.success (.of result)) finalSupply ↔
    ∃ (c₁ : SpecTec.context) (middle : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context,
          SpecTec.SpecTecCall.Func_ok c f⟩)
        n (.success (.of c₁)) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context,
          SpecTec.SpecTecCall.Funcs_ok c₁ fs⟩)
        middle (.success (.of result)) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Funcs_ok:clause:0» c (f :: fs))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«Funcs_ok:clause:1» c (f :: fs)] ()))
        n (.success (.of result)) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        unfold SpecTec.«Funcs_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hguard htail =>
          cases hguard with
          | guard_true _ =>
            cases htail with
            | bind_success hhead htail =>
              rename_i middle c₁
              cases htail with
              | bind_success hrest hpure =>
                cases hpure with
                | pure => exact ⟨c₁, middle, hhead, hrest⟩
      | orElse_unmatch _ htail =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.orElse (SpecTec.«Funcs_ok:clause:1» c (f :: fs))
            (fun _ => .unmatch))
          n (.success (.of result)) finalSupply at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Funcs_ok:clause:1» at hsecond
          cases hsecond with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond => simp at hcond
        | orElse_unmatch _ hnone => cases hnone
  · rintro ⟨c₁, middle, hhead, hrest⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.Funcs_ok_clauses c (f :: fs)) ())
      n (.success (.of result)) finalSupply
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Funcs_ok:clause:0» c (f :: fs))
      n (.success (.of result)) finalSupply
    unfold SpecTec.«Funcs_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · apply SpecTecExecution.Eval.guard_true
      rfl
    · apply SpecTecExecution.Eval.bind_success hhead
      apply SpecTecExecution.Eval.bind_success hrest
      exact SpecTecExecution.Eval.pure result

theorem funcs_success_iff_result (c : SpecTec.context)
    (fs : List SpecTec.func) (result : SpecTec.context)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Funcs_ok c fs⟩)
      n (.success (.of result)) finalSupply ↔
    funcsResult c fs = some result ∧ finalSupply = n := by
  induction fs generalizing c result n finalSupply with
  | nil =>
    constructor
    · intro h
      have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
        intro request x y hp
        cases hp
      obtain ⟨hout, hsupply⟩ :=
        SpecTecExecution.eval_deterministic hdet h
          (funcs_nil_total c n)
      cases hout
      exact ⟨rfl, hsupply⟩
    · rintro ⟨hresult, hsupply⟩
      simp [funcsResult] at hresult
      cases hresult
      cases hsupply
      exact funcs_nil_total c n
  | cons f fs ih =>
    constructor
    · intro h
      obtain ⟨c₁, middle, hhead, htail⟩ :=
        (funcs_cons_success_iff c f fs result n finalSupply).1 h
      obtain ⟨hheadResult, hmiddle⟩ :=
        (FuncDeclValidation.func_ok_success_iff_result
          c f c₁ n middle).1 hhead
      obtain ⟨htailResult, hsupply⟩ :=
        (ih c₁ result middle finalSupply).1 htail
      cases hmiddle
      exact ⟨by simp [funcsResult, hheadResult, htailResult], hsupply⟩
    · rintro ⟨hresult, hsupply⟩
      cases hhead : FuncDeclValidation.funcDeclResult c f with
      | none => simp [funcsResult, hhead] at hresult
      | some c₁ =>
        have htail : funcsResult c₁ fs = some result := by
          simpa [funcsResult, hhead] using hresult
        apply (funcs_cons_success_iff c f fs result n finalSupply).2
        exact ⟨c₁, n,
          (FuncDeclValidation.func_ok_success_iff_result c f c₁ n n).2
            ⟨hhead, rfl⟩,
          (ih c₁ result n finalSupply).2 ⟨htail, hsupply⟩⟩

theorem funcs_none (c : SpecTec.context)
    (fs : List SpecTec.func) (n : Nat)
    (hresult : funcsResult c fs = none) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Funcs_ok c fs⟩)
      n .unmatch n := by
  induction fs generalizing c with
  | nil => simp [funcsResult] at hresult
  | cons f fs ih =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.Funcs_ok_clauses c (f :: fs)) ())
      n .unmatch n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Funcs_ok:clause:0» c (f :: fs))
        n .unmatch n
      unfold SpecTec.«Funcs_ok:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · cases hhead : FuncDeclValidation.funcDeclResult c f with
        | none =>
          apply SpecTecExecution.Eval.bind_unmatch
          exact FuncDeclValidation.func_ok_none c f n hhead
        | some c₁ =>
          have htail : funcsResult c₁ fs = none := by
            simpa [funcsResult, hhead] using hresult
          apply SpecTecExecution.Eval.bind_success
            ((FuncDeclValidation.func_ok_success_iff_result
              c f c₁ n n).2 ⟨hhead, rfl⟩)
          apply SpecTecExecution.Eval.bind_unmatch
          exact ih c₁ htail
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«Funcs_ok:clause:1» c (f :: fs))
          n .unmatch n
        unfold SpecTec.«Funcs_ok:clause:1»
        apply SpecTecExecution.Eval.bind_unmatch
        apply SpecTecExecution.Eval.guard_false
        simp
      · exact SpecTecExecution.firstSuccess_nil () n

def funcsOutcome (c : SpecTec.context) (fs : List SpecTec.func) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match funcsResult c fs with
  | none => .unmatch
  | some result => .success (.of result)

theorem funcs_total (c : SpecTec.context)
    (fs : List SpecTec.func) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Funcs_ok c fs⟩)
      n (funcsOutcome c fs) n := by
  cases hresult : funcsResult c fs with
  | none =>
    simpa [funcsOutcome, hresult] using
      funcs_none c fs n hresult
  | some result =>
    simpa [funcsOutcome, hresult] using
      (funcs_success_iff_result c fs result n n).2
        ⟨hresult, rfl⟩

theorem funcs_deterministic (c : SpecTec.context)
    (fs : List SpecTec.func) (n finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Funcs_ok c fs⟩)
      n outcome finalSupply) :
    outcome = funcsOutcome c fs ∧ finalSupply = n := by
  have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
    intro request a b hp
    cases hp
  exact SpecTecExecution.eval_deterministic hdet h
    (funcs_total c fs n)

end properties.wasm_module_ok.FuncsValidation
