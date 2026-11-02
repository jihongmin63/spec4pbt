import properties.wasm_module_ok.ConstTargetCandidate

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchValtypeShape

theorem match_valtype_true_shape
    (c : SpecTec.context) (u t : SpecTec.valtype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_valtype» c.TYPES u t⟩)
      start (.success (.of true)) fin) :
    u = .BotT ∨
      (∃ a b : SpecTec.numtype,
        u = .NumT a ∧ t = .NumT b) ∨
      (∃ a b : SpecTec.vectype,
        u = .VecT a ∧ t = .VecT b) ∨
      (∃ a b : SpecTec.reftype,
        u = .RefT a ∧ t = .RefT b) := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$match_valtype_clauses» c.TYPES u t))
      start (.success (.of true)) fin at hbody
    obtain ⟨idx, hselected⟩ :=
      (SpecTecExecution.tryClauses_success_iff
        (SpecTec.«$match_valtype_clauses» c.TYPES u t)
        start (.of true) fin).1 hbody
    unfold SpecTec.«$match_valtype_clauses» at hselected
    cases hselected with
    | here h0 =>
      unfold SpecTec.«$match_valtype:clause:0» at h0
      cases h0 with
      | bind_success hguard htail =>
        cases hguard with
        | guard_true hg =>
          cases u with
          | NumT a =>
            cases htail with
            | bind_success hguard2 htail2 =>
              cases hguard2 with
              | guard_true ht =>
                cases t with
                | NumT b => exact Or.inr (Or.inl ⟨a, b, rfl, rfl⟩)
                | VecT _ => simp [SpecTec.«exec:match:valtype:NumT»] at ht
                | RefT _ => simp [SpecTec.«exec:match:valtype:NumT»] at ht
                | BotT => simp [SpecTec.«exec:match:valtype:NumT»] at ht
          | VecT _ => simp [SpecTec.«exec:match:valtype:NumT»] at hg
          | RefT _ => simp [SpecTec.«exec:match:valtype:NumT»] at hg
          | BotT => simp [SpecTec.«exec:match:valtype:NumT»] at hg
    | next _ hselected =>
      cases hselected with
      | here h1 =>
        unfold SpecTec.«$match_valtype:clause:1» at h1
        cases h1 with
        | bind_success hguard htail =>
          cases hguard with
          | guard_true hg =>
            cases u with
            | VecT a =>
              cases htail with
              | bind_success hguard2 htail2 =>
                cases hguard2 with
                | guard_true ht =>
                  cases t with
                  | VecT b => exact Or.inr (Or.inr (Or.inl ⟨a, b, rfl, rfl⟩))
                  | NumT _ => simp [SpecTec.«exec:match:valtype:VecT»] at ht
                  | RefT _ => simp [SpecTec.«exec:match:valtype:VecT»] at ht
                  | BotT => simp [SpecTec.«exec:match:valtype:VecT»] at ht
            | NumT _ => simp [SpecTec.«exec:match:valtype:VecT»] at hg
            | RefT _ => simp [SpecTec.«exec:match:valtype:VecT»] at hg
            | BotT => simp [SpecTec.«exec:match:valtype:VecT»] at hg
      | next _ hselected =>
        cases hselected with
        | here h2 =>
          unfold SpecTec.«$match_valtype:clause:2» at h2
          cases h2 with
          | bind_success hguard htail =>
            cases hguard with
            | guard_true hg =>
              cases u with
              | RefT a =>
                cases htail with
                | bind_success hguard2 htail2 =>
                  cases hguard2 with
                  | guard_true ht =>
                    cases t with
                    | RefT b => exact Or.inr (Or.inr (Or.inr ⟨a, b, rfl, rfl⟩))
                    | NumT _ => simp [SpecTec.«exec:match:valtype:RefT»] at ht
                    | VecT _ => simp [SpecTec.«exec:match:valtype:RefT»] at ht
                    | BotT => simp [SpecTec.«exec:match:valtype:RefT»] at ht
              | NumT _ => simp [SpecTec.«exec:match:valtype:RefT»] at hg
              | VecT _ => simp [SpecTec.«exec:match:valtype:RefT»] at hg
              | BotT => simp [SpecTec.«exec:match:valtype:RefT»] at hg
        | next _ hselected =>
          cases hselected with
          | here h3 =>
            unfold SpecTec.«$match_valtype:clause:3» at h3
            cases h3 with
            | bind_success hguard _ =>
              cases hguard with
              | guard_true hg =>
                cases u with
                | BotT => exact Or.inl rfl
                | NumT _ => simp [SpecTec.«exec:match:valtype:BotT»] at hg
                | VecT _ => simp [SpecTec.«exec:match:valtype:BotT»] at hg
                | RefT _ => simp [SpecTec.«exec:match:valtype:BotT»] at hg
          | next _ hselected =>
            cases hselected with
            | here h4 =>
              change SpecTecExecution.Eval SpecTec.Body
                (.pure false) start (.success (.of true)) fin at h4
              cases h4
            | next _ hnone => cases hnone

end properties.wasm_module_ok.MatchValtypeShape
