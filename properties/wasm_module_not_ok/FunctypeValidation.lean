import properties.wasm_module_not_ok.ResulttypeValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem resulttype_ok_success_iff_valid (c : SpecTec.context)
    (ts : SpecTec.resulttype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Resulttype_ok c ts⟩)
      start (.success (.of ())) finalSupply ↔
    resulttypesValid c ts = true ∧ finalSupply = start := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Resulttype_ok:clause:0» c ts)
          (fun _ => .unmatch))
        start (.success (.of ())) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        unfold SpecTec.«Resulttype_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hiter hpure =>
          cases hpure with
          | pure =>
            exact (resulttype_iter0_success_iff_valid c ts start finalSupply).1 hiter
      | orElse_unmatch _ htail => cases htail
  · rintro ⟨hvalid, rfl⟩
    have hiter :=
      (resulttype_iter0_success_iff_valid c ts finalSupply finalSupply).2
        ⟨hvalid, rfl⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.Resulttype_ok_clauses c ts) ())
      finalSupply (.success (.of ())) finalSupply
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Resulttype_ok:clause:0» c ts)
      finalSupply (.success (.of ())) finalSupply
    unfold SpecTec.«Resulttype_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success hiter
    exact SpecTecExecution.Eval.pure ()

def functypeValid (c : SpecTec.context) (ft : SpecTec.functype) : Bool :=
  match ft with
  | .FuncT params results =>
      resulttypesValid c params && resulttypesValid c results

theorem functype_ok_success_iff_valid (c : SpecTec.context)
    (ft : SpecTec.functype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Functype_ok c ft⟩)
      start (.success (.of ())) finalSupply ↔
    functypeValid c ft = true ∧ finalSupply = start := by
  cases ft with
  | FuncT params results =>
      constructor
      · intro h
        cases h with
        | call hbody =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse
              (SpecTec.«Functype_ok:clause:0» c (.FuncT params results))
              (fun _ => .unmatch))
            start (.success (.of ())) finalSupply at hbody
          cases hbody with
          | orElse_success hfirst =>
            unfold SpecTec.«Functype_ok:clause:0» at hfirst
            cases hfirst with
            | bind_success hparams hrest =>
              cases hrest with
              | bind_success hresults hpure =>
                cases hpure with
                | pure =>
                  obtain ⟨hp, hm⟩ :=
                    (resulttype_ok_success_iff_valid c params start _).1 hparams
                  obtain ⟨hr, hf⟩ :=
                    (resulttype_ok_success_iff_valid c results _ finalSupply).1 hresults
                  constructor
                  · simp [functypeValid, hp, hr]
                  · omega
          | orElse_unmatch _ htail => cases htail
      · rintro ⟨hvalid, rfl⟩
        have hsplit : resulttypesValid c params = true ∧
            resulttypesValid c results = true := by
          simpa [functypeValid] using hvalid
        have hparams :=
          (resulttype_ok_success_iff_valid c params finalSupply finalSupply).2
            ⟨hsplit.1, rfl⟩
        have hresults :=
          (resulttype_ok_success_iff_valid c results finalSupply finalSupply).2
            ⟨hsplit.2, rfl⟩
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.Functype_ok_clauses c (.FuncT params results)) ())
          finalSupply (.success (.of ())) finalSupply
        apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«Functype_ok:clause:0» c (.FuncT params results))
          finalSupply (.success (.of ())) finalSupply
        unfold SpecTec.«Functype_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success hparams
        apply SpecTecExecution.Eval.bind_success hresults
        exact SpecTecExecution.Eval.pure ()

end properties.wasm_module_not_ok.Rejection
