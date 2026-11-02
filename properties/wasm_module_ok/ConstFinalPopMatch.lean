import properties.wasm_module_ok.ConstFinalPopShape

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstFinalPopMatch

theorem final_const_pop_matches
    (c : SpecTec.context) (t u : SpecTec.valtype)
    (ellipses : SpecTec.ellipses) (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$pop» c
          (.NoEllipses, [t]) (.NoEllipses, [u])⟩)
      start (.success (.of
        (ellipses, ([] : List SpecTec.valtype)))) fin) :
    ∃ before after : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.Match_resulttype c [u] [t]⟩)
        before (.success (.of ())) after := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$pop_clauses» c
          (.NoEllipses, [t]) (.NoEllipses, [u])) ())
      start (.success (.of (ellipses, []))) fin at hbody
    obtain ⟨idx, hselected⟩ :=
      (SpecTecExecution.firstSuccess_success_iff
        (SpecTec.«$pop_clauses» c
          (.NoEllipses, [t]) (.NoEllipses, [u])) ()
        start (.of (ellipses, [])) fin).1 hbody
    unfold SpecTec.«$pop_clauses» at hselected
    cases hselected with
    | here h0 =>
      unfold SpecTec.«$pop:clause:0» at h0
      cases h0 with
      | bind_success hguard _ =>
        cases hguard with
        | guard_true hg => simp [SpecTec.«exec:match:ellipses:Ellipses»] at hg
    | next _ hselected =>
      cases hselected with
      | here h1 =>
        unfold SpecTec.«$pop:clause:1» at h1
        cases h1 with
        | bind_success _ htail =>
          cases htail with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hg => simp [SpecTec.«exec:match:ellipses:Ellipses»] at hg
      | next _ hselected =>
        cases hselected with
        | here h2 =>
          unfold SpecTec.«$pop:clause:2» at h2
          cases h2 with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hg => simp [SpecTec.«exec:match:ellipses:Ellipses»] at hg
        | next _ hselected =>
          cases hselected with
          | here h3 =>
            unfold SpecTec.«$pop:clause:3» at h3
            cases h3 with
            | bind_success _ htail =>
              cases htail with
              | bind_success _ htail =>
                cases htail with
                | bind_success hmin htail =>
                  have hminval := (MinValidation.min_success_iff
                    1 1 _ _ _).1 hmin
                  rcases hminval with ⟨rfl, rfl⟩
                  simp at htail
                  cases htail with
                  | bind_success _ htail =>
                    simp at htail
                    cases htail with
                    | bind_success _ htail =>
                      cases htail with
                      | bind_success hmatch _ =>
                        simp at hmatch
                        exact ⟨_, _, by simpa using SpecTecExecution.Eval.call hmatch⟩
          | next _ hnone => cases hnone

end properties.wasm_module_ok.ConstFinalPopMatch
