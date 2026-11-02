import properties.wasm_module_ok.RectypeLengthValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.RectypePositionValidation

theorem rectype_subst_iter_position
    (c : SpecTec.context) (rolled substituted : List SpecTec.deftype)
    (start finish i : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List SpecTec.deftype,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:2» c rolled⟩)
      start (.success (.of substituted)) finish)
    (hi : i < rolled.length) :
    ∃ dt dt' : SpecTec.deftype,
      rolled[i]? = some dt ∧ substituted[i]? = some dt' ∧
      ∃ before after : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.deftype,
          SpecTec.SpecTecCall.«$subst_deftype»
            (List SpecTec.deftype) c.TYPES
            SpecTec.SpecTecCall.«$subst_of» dt⟩)
        before (.success (.of dt')) after := by
  induction rolled generalizing substituted start finish i with
  | nil => simp at hi
  | cons hd tl ih =>
      cases h with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.«Rectype_ok:rule:iter:2_clauses» c (hd :: tl)) ())
          start (.success (.of substituted)) finish at hbody
        obtain ⟨idx, hselected⟩ :=
          (SpecTecExecution.firstSuccess_success_iff
            (SpecTec.«Rectype_ok:rule:iter:2_clauses» c (hd :: tl)) ()
            start (.of substituted) finish).1 hbody
        unfold SpecTec.«Rectype_ok:rule:iter:2_clauses» at hselected
        cases hselected with
        | here h0 =>
          unfold SpecTec.«Rectype_ok:rule:iter:2:clause:0» at h0
          cases h0
        | next _ hrest =>
          cases hrest with
          | here h1 =>
            unfold SpecTec.«Rectype_ok:rule:iter:2:clause:1» at h1
            cases h1 with
            | bind_success hhead htail =>
              rename_i hd'
              cases htail with
              | bind_success hrec hpure =>
                rename_i tail'
                cases hpure
                cases i with
                | zero =>
                    exact ⟨hd, hd', rfl, rfl, _, _, hhead⟩
                | succ j =>
                    have hj : j < tl.length := by simpa using hi
                    obtain ⟨dt, dt', hget, hget', before, after, hsubst⟩ :=
                      ih tail' _ _ j hrec hj
                    exact ⟨dt, dt', hget, hget', before, after, hsubst⟩
          | next _ hrest => cases hrest

end properties.wasm_module_ok.RectypePositionValidation
