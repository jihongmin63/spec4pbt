import properties.wasm_module_ok.RolledPositionValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.RectypeAppendedPosition

open properties.wasm_module_not_ok.Rejection

theorem rectype_ok_appended_position_subst
    (c c' : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of c')) finish) :
    ∃ dts : List SpecTec.deftype,
      c' = {c with TYPES := c.TYPES ++ dts} ∧
      (∀ i : Nat, i < sts.length →
        ∃ dt' : SpecTec.deftype,
          dts[i]? = some dt' ∧
          ∃ before after : Nat,
            SpecTecExecution.Eval SpecTec.Body
              (.call ⟨SpecTec.deftype,
                SpecTec.Call.«$subst_deftype»
                  (List SpecTec.deftype) c.TYPES
                  SpecTec.Call.«$subst_of»
                  (.DefT
                    (.RecT (rollSubtypes sts c.TYPES.length
                      (sts.length + c.TYPES.length))) i)⟩)
              before (.success (.of dt')) after) := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Rectype_ok_clauses c (.RecT sts)))
      start (.success (.of c')) finish at hbody
    obtain ⟨idx, hselected⟩ :=
      (SpecTecExecution.tryClauses_success_iff
        (SpecTec.Rectype_ok_clauses c (.RecT sts))
        start (.of c') finish).1 hbody
    unfold SpecTec.Rectype_ok_clauses at hselected
    cases hselected with
    | here h0 =>
      unfold SpecTec.«Rectype_ok:clause:0» at h0
      dsimp only at h0
      cases h0 with
      | bind_success hrange h1 =>
        dsimp only at h1
        cases h1 with
        | bind_success hroll h2 =>
          rename_i rolled
          have hrolled : rolled = rollDeftypes c.TYPES.length (.RecT sts) := by
            obtain ⟨hout, _⟩ := rolldt_deterministic
              c.TYPES.length (.RecT sts) _ _ (.success (.of rolled)) hroll
            cases hout
            rfl
          dsimp only at h2
          cases h2 with
          | bind_success hsubst h3 =>
            rename_i dts
            dsimp only at h3
            cases h3 with
            | bind_success hiter5 h4 =>
              dsimp only at h4
              cases h4 with
              | bind_success hguard h5 =>
                dsimp only at h5
                cases h5 with
                | bind_success hiter6 h6 =>
                  rename_i v
                  cases h6
                  cases v
                  refine ⟨dts, rfl, ?_⟩
                  intro i hi
                  have hirolled : i < rolled.length := by
                    rw [hrolled]
                    rw [properties.wasm_module_ok.RectypeLengthValidation.rollDeftypes_length]
                    exact hi
                  obtain ⟨dt, dt', hget, hget', before, after, hcall⟩ :=
                    properties.wasm_module_ok.RectypePositionValidation.rectype_subst_iter_position
                      c rolled dts _ _ i hsubst hirolled
                  rw [hrolled] at hget
                  have hrget := properties.wasm_module_ok.RolledPositionValidation.rollDeftypes_get?
                    c.TYPES.length sts i hi
                  rw [hget] at hrget
                  cases hrget
                  exact ⟨dt', hget', before, after, hcall⟩
    | next _ hrest => cases hrest

end properties.wasm_module_ok.RectypeAppendedPosition
