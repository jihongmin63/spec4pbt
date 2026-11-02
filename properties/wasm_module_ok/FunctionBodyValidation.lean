import properties.wasm_module_ok.bundle.Helpers

set_option autoImplicit false

namespace properties.wasm_module_ok.FunctionBodyValidation

def parameterLocals (ts : List SpecTec.valtype) : List SpecTec.localtype :=
  ts.map (SpecTec.localtype.LocalT SpecTec.init.Set)

theorem parameter_locals_total (ts : List SpecTec.valtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List SpecTec.localtype,
        SpecTec.SpecTecCall.«Funcbody_ok:rule:iter:2» ts⟩)
      n (.success (.of (parameterLocals ts))) n := by
  induction ts generalizing n with
  | nil =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«Funcbody_ok:rule:iter:2_clauses» []) ())
      n (.success (.of (parameterLocals []))) n
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Funcbody_ok:rule:iter:2:clause:0» [])
      n (.success (.of (parameterLocals []))) n
    exact SpecTecExecution.Eval.pure []
  | cons t ts ih =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«Funcbody_ok:rule:iter:2_clauses» (t :: ts)) ())
      n (.success (.of (parameterLocals (t :: ts)))) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Funcbody_ok:rule:iter:2:clause:0» (t :: ts))
        n .unmatch n
      exact SpecTecExecution.Eval.unmatch
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Funcbody_ok:rule:iter:2:clause:1» (t :: ts))
        n (.success (.of (parameterLocals (t :: ts)))) n
      unfold SpecTec.«Funcbody_ok:rule:iter:2:clause:1»
      apply SpecTecExecution.Eval.bind_success (ih n)
      exact SpecTecExecution.Eval.pure (parameterLocals (t :: ts))

theorem parameter_locals_success_iff
    (ts : List SpecTec.valtype) (n finalSupply : Nat)
    (result : List SpecTec.localtype) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List SpecTec.localtype,
        SpecTec.SpecTecCall.«Funcbody_ok:rule:iter:2» ts⟩)
      n (.success (.of result)) finalSupply ↔
      result = parameterLocals ts ∧ finalSupply = n := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet h (parameter_locals_total ts n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact parameter_locals_total ts finalSupply

theorem funcbody_iter_nil_success (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.«Module_ok:rule:iter:2» c []⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«Module_ok:rule:iter:2_clauses» c []) ())
    n (.success (.of ())) n
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Module_ok:rule:iter:2:clause:0» c [])
    n (.success (.of ())) n
  exact SpecTecExecution.Eval.pure ()

theorem funcbody_iter_cons_success_iff
    (c : SpecTec.context) (f : SpecTec.func) (fs : List SpecTec.func)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.«Module_ok:rule:iter:2» c (f :: fs)⟩)
      n (.success (.of ())) finalSupply ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Funcbody_ok c f⟩)
        n (.success (.of ())) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.«Module_ok:rule:iter:2» c fs⟩)
        middle (.success (.of ())) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«Module_ok:rule:iter:2_clauses» c (f :: fs)) ())
        n (.success (.of ())) finalSupply at hbody
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Module_ok:rule:iter:2:clause:0» c (f :: fs))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«Module_ok:rule:iter:2:clause:1» c (f :: fs)] ()))
        n (.success (.of ())) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.unmatch) n (.success (.of ())) finalSupply at hfirst
        cases hfirst
      | orElse_unmatch _ htail =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.orElse (SpecTec.«Module_ok:rule:iter:2:clause:1» c (f :: fs))
            (fun _ => .unmatch))
          n (.success (.of ())) finalSupply at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Module_ok:rule:iter:2:clause:1» at hsecond
          cases hsecond with
          | bind_success hfunc htail =>
            cases htail with
            | bind_success hrest hpure =>
              cases hpure with
              | pure => exact ⟨_, hfunc, hrest⟩
        | orElse_unmatch _ hlast => cases hlast
  · rintro ⟨middle, hfunc, hrest⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«Module_ok:rule:iter:2_clauses» c (f :: fs)) ())
      n (.success (.of ())) finalSupply
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Module_ok:rule:iter:2:clause:0» c (f :: fs))
        n .unmatch n
      exact SpecTecExecution.Eval.unmatch
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Module_ok:rule:iter:2:clause:1» c (f :: fs))
        n (.success (.of ())) finalSupply
      unfold SpecTec.«Module_ok:rule:iter:2:clause:1»
      apply SpecTecExecution.Eval.bind_success hfunc
      apply SpecTecExecution.Eval.bind_success hrest
      exact SpecTecExecution.Eval.pure ()

end properties.wasm_module_ok.FunctionBodyValidation
