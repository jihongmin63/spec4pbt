import properties.wasm_module_not_ok.MatchStructtypeTrace

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem match_storagetype_pack_total (d : List SpecTec.deftype)
    (a b : SpecTec.packtype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_storagetype» d
        (.PackStorageT a) (.PackStorageT b)⟩)
      start (.success (.of (decide (a = b)))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_storagetype_clauses» d
        (.PackStorageT a) (.PackStorageT b)) ())
    start (.success (.of (decide (a = b)))) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_storagetype:clause:0» d
        (.PackStorageT a) (.PackStorageT b)) start .unmatch start
    unfold SpecTec.«$match_storagetype:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false
      (by simp [SpecTec.«exec:match:storagetype:ValStorageT»])
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_storagetype:clause:1» d
        (.PackStorageT a) (.PackStorageT b))
      start (.success (.of (decide (a = b)))) start
    unfold SpecTec.«$match_storagetype:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true
        (by simp [SpecTec.«exec:match:storagetype:PackStorageT»])
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          (by simp [SpecTec.«exec:match:storagetype:PackStorageT»])
      · apply SpecTecExecution.Eval.bind_success
          (match_packtype_total d a b start)
        exact SpecTecExecution.Eval.pure (decide (a = b))

theorem match_storagetype_pack_deterministic
    (d : List SpecTec.deftype) (a b : SpecTec.packtype)
    (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_storagetype» d
        (.PackStorageT a) (.PackStorageT b)⟩)
      start outcome finalSupply) :
    outcome = .success (.of (decide (a = b))) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (match_storagetype_pack_total d a b start)

theorem match_storagetype_val_true_iff (d : List SpecTec.deftype)
    (a b : SpecTec.valtype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_storagetype» d
        (.ValStorageT a) (.ValStorageT b)⟩)
      start (.success (.of true)) finalSupply ↔
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_valtype» d a b⟩)
      start (.success (.of true)) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse
          (SpecTec.«$match_storagetype:clause:0» d
            (.ValStorageT a) (.ValStorageT b))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«$match_storagetype:clause:1» d
              (.ValStorageT a) (.ValStorageT b),
             fun _ => SpecTec.«$match_storagetype:clause:2» d
              (.ValStorageT a) (.ValStorageT b)] ()))
        start (.success (.of true)) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
          unfold SpecTec.«$match_storagetype:clause:0» at hfirst
          cases hfirst with
          | bind_success hg1 hrest =>
              cases hg1 with
              | guard_true _ =>
                  cases hrest with
                  | bind_success hg2 hrest =>
                      cases hg2 with
                      | guard_true _ =>
                          cases hrest with
                          | bind_success hchild hpure =>
                              cases hpure with
                              | pure => exact hchild
      | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse
              (SpecTec.«$match_storagetype:clause:1» d
                (.ValStorageT a) (.ValStorageT b))
              (fun _ => SpecTecExecution.firstSuccess
                [fun _ => SpecTec.«$match_storagetype:clause:2» d
                  (.ValStorageT a) (.ValStorageT b)] ()))
            start (.success (.of true)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
              unfold SpecTec.«$match_storagetype:clause:1» at hsecond
              cases hsecond with
              | bind_success hg _ =>
                  cases hg with
                  | guard_true hbad => cases hbad
          | orElse_unmatch _ htail2 =>
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (.orElse
                  (SpecTec.«$match_storagetype:clause:2» d
                    (.ValStorageT a) (.ValStorageT b)) (fun _ => .unmatch))
                start (.success (.of true)) finalSupply at htail2
              cases htail2 with
              | orElse_success hlast =>
                  change SpecTecExecution.Eval SpecTec.specTecProgram
                    (.pure false) start (.success (.of true)) finalSupply
                    at hlast
                  cases hlast
              | orElse_unmatch _ hnil => cases hnil
  · intro hchild
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$match_storagetype_clauses» d
          (.ValStorageT a) (.ValStorageT b)) ())
      start (.success (.of true)) finalSupply
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_storagetype:clause:0» d
        (.ValStorageT a) (.ValStorageT b))
      start (.success (.of true)) finalSupply
    unfold SpecTec.«$match_storagetype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true
        (by simp [SpecTec.«exec:match:storagetype:ValStorageT»])
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          (by simp [SpecTec.«exec:match:storagetype:ValStorageT»])
      · apply SpecTecExecution.Eval.bind_success hchild
        exact SpecTecExecution.Eval.pure true

end properties.wasm_module_not_ok.Rejection
