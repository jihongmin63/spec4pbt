import properties.wasm_module_ok.TableProvenance

set_option autoImplicit false

namespace properties.wasm_module_ok.ElemModeBaseDecision

theorem passive_total (c : SpecTec.context)
    (rt : SpecTec.reftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Elemmode_ok c rt .Passive⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.Elemmode_ok_clauses c rt .Passive) ())
    n (.success (.of ())) n
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Elemmode_ok:clause:0» c rt .Passive)
    n (.success (.of ())) n
  unfold SpecTec.«Elemmode_ok:clause:0»
  exact SpecTecExecution.Eval.bind_success
    (SpecTecExecution.Eval.guard_true (by decide))
    (SpecTecExecution.Eval.pure ())

theorem declarative_total (c : SpecTec.context)
    (rt : SpecTec.reftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Elemmode_ok c rt .Declarative⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.Elemmode_ok_clauses c rt .Declarative) ())
    n (.success (.of ())) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Elemmode_ok:clause:0» c rt .Declarative)
      n .unmatch n
    unfold SpecTec.«Elemmode_ok:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Elemmode_ok:clause:1» c rt .Declarative)
      n .unmatch n
    unfold SpecTec.«Elemmode_ok:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by decide))
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Elemmode_ok:clause:2» c rt .Declarative)
    n (.success (.of ())) n
  unfold SpecTec.«Elemmode_ok:clause:2»
  exact SpecTecExecution.Eval.bind_success
    (SpecTecExecution.Eval.guard_true (by decide))
    (SpecTecExecution.Eval.pure ())

theorem passive_success_iff (c : SpecTec.context)
    (rt : SpecTec.reftype) (start finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Elemmode_ok c rt .Passive⟩)
      start (.success (.of ())) finish ↔ finish = start := by
  constructor
  · intro hcall
    have hdet : SpecTecExecution.PrimitiveDeterministic
        SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    exact (SpecTecExecution.eval_deterministic hdet hcall
      (passive_total c rt start)).2
  · intro hfinish
    subst finish
    exact passive_total c rt start

theorem declarative_success_iff (c : SpecTec.context)
    (rt : SpecTec.reftype) (start finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Elemmode_ok c rt .Declarative⟩)
      start (.success (.of ())) finish ↔ finish = start := by
  constructor
  · intro hcall
    have hdet : SpecTecExecution.PrimitiveDeterministic
        SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    exact (SpecTecExecution.eval_deterministic hdet hcall
      (declarative_total c rt start)).2
  · intro hfinish
    subst finish
    exact declarative_total c rt start

end properties.wasm_module_ok.ElemModeBaseDecision
