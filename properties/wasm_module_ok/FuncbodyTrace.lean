import properties.wasm_module_ok.FunctionTypeValidation
import properties.wasm_module_ok.FunctionBodyValidation
import properties.wasm_module_ok.LocalListValidation
import properties.wasm_module_ok.BlockTrace

set_option autoImplicit false

namespace properties.wasm_module_ok.FuncbodyTrace

def bodyContext (c : SpecTec.context)
    (args results : List SpecTec.valtype)
    (locals : List SpecTec.localtype) : SpecTec.context :=
  { { { c with
      LOCALS := FunctionBodyValidation.parameterLocals args ++ locals } with
      RESULTS := results } with LABELS := [results] }

theorem funcbody_success_iff
    (c : SpecTec.context) (f : SpecTec.func)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Funcbody_ok c f⟩)
      n (.success (.of ())) finalSupply ↔
    ∃ (args results : List SpecTec.valtype)
      (locals : List SpecTec.localtype) (middle₁ middle₂ : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.functype,
          SpecTec.SpecTecCall.«$func_type» c f.FTYPE⟩)
        n (.success (.of (SpecTec.functype.FuncT args results))) middle₁ ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨List SpecTec.localtype,
          SpecTec.SpecTecCall.«Funcbody_ok:rule:iter:1» c f.LOCALS⟩)
        middle₁ (.success (.of locals)) middle₂ ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Block_ok
          (bodyContext c args results locals)
          (SpecTec.instrtype.InstrT [] results []) f.BODY⟩)
        middle₂ (.success (.of ())) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Funcbody_ok:clause:0» c f)
          (fun _ => .unmatch))
        n (.success (.of ())) finalSupply at hbody
      cases hbody with
      | orElse_success hclause =>
        unfold SpecTec.«Funcbody_ok:clause:0» at hclause
        cases hclause with
        | bind_success htype htail =>
          rename_i middle₁ ft
          cases ft with
          | FuncT args results =>
            cases htail with
            | bind_success hlocals htail =>
              rename_i middle₂ locals
              cases htail with
              | bind_success hparams htail =>
                rename_i middle₃ params
                obtain ⟨hparams_eq, hsupply⟩ :=
                  (FunctionBodyValidation.parameter_locals_success_iff
                    args middle₂ middle₃ params).1 hparams
                subst params
                subst middle₃
                cases htail with
                | bind_success hblock hpure =>
                  cases hpure with
                  | pure => exact ⟨args, results, locals, middle₁,
                      middle₂, htype, hlocals, hblock⟩
      | orElse_unmatch _ hlast => cases hlast
  · rintro ⟨args, results, locals, middle₁, middle₂,
      htype, hlocals, hblock⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.Funcbody_ok_clauses c f) ())
      n (.success (.of ())) finalSupply
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Funcbody_ok:clause:0» c f)
      n (.success (.of ())) finalSupply
    unfold SpecTec.«Funcbody_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success htype
    apply SpecTecExecution.Eval.bind_success hlocals
    apply SpecTecExecution.Eval.bind_success
      (FunctionBodyValidation.parameter_locals_total args middle₂)
    apply SpecTecExecution.Eval.bind_success hblock
    exact SpecTecExecution.Eval.pure ()

theorem funcbody_success_iff_local_valid
    (c : SpecTec.context) (f : SpecTec.func)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Funcbody_ok c f⟩)
      n (.success (.of ())) finalSupply ↔
    ∃ (args results : List SpecTec.valtype) (middle : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.functype,
          SpecTec.SpecTecCall.«$func_type» c f.FTYPE⟩)
        n (.success (.of (SpecTec.functype.FuncT args results))) middle ∧
      LocalListValidation.allLocalsValid c f.LOCALS = true ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Block_ok
          (bodyContext c args results
            (LocalListValidation.localTypes f.LOCALS))
          (SpecTec.instrtype.InstrT [] results []) f.BODY⟩)
        middle (.success (.of ())) finalSupply := by
  constructor
  · intro h
    obtain ⟨args, results, locals, middle₁, middle₂,
      htype, hlocals, hblock⟩ :=
      (funcbody_success_iff c f n finalSupply).1 h
    obtain ⟨hvalid, hresult, hsupply⟩ :=
      (LocalListValidation.local_iter_success_iff_valid
        c f.LOCALS locals middle₁ middle₂).1 hlocals
    subst locals
    subst middle₂
    exact ⟨args, results, middle₁, htype, hvalid, hblock⟩
  · rintro ⟨args, results, middle, htype, hvalid, hblock⟩
    apply (funcbody_success_iff c f n finalSupply).2
    exact ⟨args, results, LocalListValidation.localTypes f.LOCALS,
      middle, middle, htype,
      (LocalListValidation.local_iter_success_iff_valid c f.LOCALS
        (LocalListValidation.localTypes f.LOCALS) middle middle).2
          ⟨hvalid, rfl, rfl⟩,
      hblock⟩

theorem funcbody_success_iff_precomputed
    (c : SpecTec.context) (f : SpecTec.func)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Funcbody_ok c f⟩)
      n (.success (.of ())) finalSupply ↔
    ∃ (args results : List SpecTec.valtype),
      FunctionTypeValidation.funcTypeResult c f.FTYPE =
        some (.FuncT args results) ∧
      LocalListValidation.allLocalsValid c f.LOCALS = true ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Block_ok
          (bodyContext c args results
            (LocalListValidation.localTypes f.LOCALS))
          (SpecTec.instrtype.InstrT [] results []) f.BODY⟩)
        n (.success (.of ())) finalSupply := by
  rw [funcbody_success_iff_local_valid]
  constructor
  · rintro ⟨args, results, middle, htype, hlocals, hblock⟩
    obtain ⟨hresult, hsupply⟩ :=
      (FunctionTypeValidation.func_type_success_iff_result
        c f.FTYPE (.FuncT args results) n middle).1 htype
    subst middle
    exact ⟨args, results, hresult, hlocals, hblock⟩
  · rintro ⟨args, results, hresult, hlocals, hblock⟩
    exact ⟨args, results, n,
      (FunctionTypeValidation.func_type_success_iff_result
        c f.FTYPE (.FuncT args results) n n).2 ⟨hresult, rfl⟩,
      hlocals, hblock⟩

end properties.wasm_module_ok.FuncbodyTrace
