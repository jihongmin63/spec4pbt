import properties.wasm_module_not_ok.MatchDeftypeBase

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem match_heaptype_exists_nil_total (d : List SpecTec.deftype)
    (dt : SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype_exists» d [] dt⟩)
      start (.success (.of false)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_exists_clauses» d [] dt) ())
    start (.success (.of false)) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_heaptype_exists:clause:0» d [] dt)
    start (.success (.of false)) start
  unfold SpecTec.«$match_heaptype_exists:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by decide)
  · exact SpecTecExecution.Eval.pure false

theorem match_heaptype_exists_nil_deterministic
    (d : List SpecTec.deftype) (dt : SpecTec.deftype)
    (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype_exists» d [] dt⟩)
      start outcome finalSupply) :
    outcome = .success (.of false) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (match_heaptype_exists_nil_total d dt start)

theorem match_heaptype_exists_cons_head_true
    (d : List SpecTec.deftype) (ht : SpecTec.heaptype)
    (hts : List SpecTec.heaptype) (dt : SpecTec.deftype)
    (start finalSupply : Nat)
    (hhead : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» d ht (.DefHT dt)⟩)
      start (.success (.of true)) finalSupply) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype_exists» d (ht :: hts) dt⟩)
      start (.success (.of true)) finalSupply := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_exists_clauses» d (ht :: hts) dt) ())
    start (.success (.of true)) finalSupply
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype_exists:clause:0» d (ht :: hts) dt)
      start .unmatch start
    unfold SpecTec.«$match_heaptype_exists:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false (by simp)
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype_exists:clause:1» d (ht :: hts) dt)
      start (.success (.of true)) finalSupply
    unfold SpecTec.«$match_heaptype_exists:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by simp)
    · apply SpecTecExecution.Eval.bind_success hhead
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · exact SpecTecExecution.Eval.pure true

theorem match_heaptype_exists_cons_tail_result
    (d : List SpecTec.deftype) (ht : SpecTec.heaptype)
    (hts : List SpecTec.heaptype) (dt : SpecTec.deftype) (result : Bool)
    (start middle finalSupply : Nat)
    (hhead : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» d ht (.DefHT dt)⟩)
      start (.success (.of false)) middle)
    (htail : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype_exists» d hts dt⟩)
      middle (.success (.of result)) finalSupply) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype_exists» d (ht :: hts) dt⟩)
      start (.success (.of result)) finalSupply := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_heaptype_exists_clauses» d (ht :: hts) dt) ())
    start (.success (.of result)) finalSupply
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_heaptype_exists:clause:0» d (ht :: hts) dt)
      start .unmatch start
    unfold SpecTec.«$match_heaptype_exists:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false (by simp)
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype_exists:clause:1» d (ht :: hts) dt)
        start .unmatch middle
      unfold SpecTec.«$match_heaptype_exists:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true (by simp)
      · apply SpecTecExecution.Eval.bind_success hhead
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false (by decide)
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_heaptype_exists:clause:2» d (ht :: hts) dt)
        start (.success (.of result)) finalSupply
      unfold SpecTec.«$match_heaptype_exists:clause:2»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true (by simp)
      · apply SpecTecExecution.Eval.bind_success hhead
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true (by decide)
        · apply SpecTecExecution.Eval.bind_success htail
          exact SpecTecExecution.Eval.pure result

theorem match_heaptype_exists_cons_tail_true
    (d : List SpecTec.deftype) (ht : SpecTec.heaptype)
    (hts : List SpecTec.heaptype) (dt : SpecTec.deftype)
    (start middle finalSupply : Nat)
    (hhead : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» d ht (.DefHT dt)⟩)
      start (.success (.of false)) middle)
    (htail : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype_exists» d hts dt⟩)
      middle (.success (.of true)) finalSupply) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype_exists» d (ht :: hts) dt⟩)
      start (.success (.of true)) finalSupply :=
  match_heaptype_exists_cons_tail_result d ht hts dt true
    start middle finalSupply hhead htail

theorem match_heaptype_exists_cons_true_iff
    (d : List SpecTec.deftype) (ht : SpecTec.heaptype)
    (hts : List SpecTec.heaptype) (dt : SpecTec.deftype)
    (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype_exists» d (ht :: hts) dt⟩)
      start (.success (.of true)) finalSupply ↔
    (SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» d ht (.DefHT dt)⟩)
      start (.success (.of true)) finalSupply) ∨
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_heaptype» d ht (.DefHT dt)⟩)
        start (.success (.of false)) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_heaptype_exists» d hts dt⟩)
        middle (.success (.of true)) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse
          (SpecTec.«$match_heaptype_exists:clause:0» d (ht :: hts) dt)
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«$match_heaptype_exists:clause:1»
              d (ht :: hts) dt,
             fun _ => SpecTec.«$match_heaptype_exists:clause:2»
              d (ht :: hts) dt] ()))
        start (.success (.of true)) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
          unfold SpecTec.«$match_heaptype_exists:clause:0» at hfirst
          cases hfirst with
          | bind_success hg _ =>
              cases hg with
              | guard_true hbad => cases hbad
      | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse
              (SpecTec.«$match_heaptype_exists:clause:1» d (ht :: hts) dt)
              (fun _ => SpecTecExecution.firstSuccess
                [fun _ => SpecTec.«$match_heaptype_exists:clause:2»
                  d (ht :: hts) dt] ()))
            start (.success (.of true)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
              unfold SpecTec.«$match_heaptype_exists:clause:1» at hsecond
              cases hsecond with
              | bind_success hg hrest =>
                  cases hg with
                  | guard_true _ =>
                      cases hrest with
                      | bind_success hhead hrest =>
                          cases hrest with
                          | bind_success hbool hpure =>
                              cases hpure with
                              | pure =>
                                  cases hbool with
                                  | guard_true htrue =>
                                      cases htrue
                                      exact Or.inl hhead
          | orElse_unmatch _ htail2 =>
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (.orElse
                  (SpecTec.«$match_heaptype_exists:clause:2»
                    d (ht :: hts) dt) (fun _ => .unmatch))
                start (.success (.of true)) finalSupply at htail2
              cases htail2 with
              | orElse_success hthird =>
                  unfold SpecTec.«$match_heaptype_exists:clause:2» at hthird
                  cases hthird with
                  | bind_success hg hrest =>
                      cases hg with
                      | guard_true _ =>
                          cases hrest with
                          | bind_success hhead hrest =>
                              rename_i headResult
                              cases hrest with
                              | bind_success hnot hrest =>
                                  cases hnot with
                                  | guard_true hfalse =>
                                      cases hrest with
                                      | bind_success hrecursive hpure =>
                                          cases hpure with
                                          | pure =>
                                              cases headResult with
                                              | true =>
                                                  exact False.elim (hfalse rfl)
                                              | false =>
                                                  exact Or.inr ⟨_, hhead,
                                                    hrecursive⟩
              | orElse_unmatch _ hnil => cases hnil
  · intro h
    cases h with
    | inl hhead =>
        exact match_heaptype_exists_cons_head_true d ht hts dt
          start finalSupply hhead
    | inr htail =>
        obtain ⟨middle, hhead, hrecursive⟩ := htail
        exact match_heaptype_exists_cons_tail_true d ht hts dt
          start middle finalSupply hhead hrecursive

theorem match_heaptype_exists_cons_false_iff
    (d : List SpecTec.deftype) (ht : SpecTec.heaptype)
    (hts : List SpecTec.heaptype) (dt : SpecTec.deftype)
    (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype_exists» d (ht :: hts) dt⟩)
      start (.success (.of false)) finalSupply ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_heaptype» d ht (.DefHT dt)⟩)
        start (.success (.of false)) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_heaptype_exists» d hts dt⟩)
        middle (.success (.of false)) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse
          (SpecTec.«$match_heaptype_exists:clause:0» d (ht :: hts) dt)
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«$match_heaptype_exists:clause:1»
              d (ht :: hts) dt,
             fun _ => SpecTec.«$match_heaptype_exists:clause:2»
              d (ht :: hts) dt] ()))
        start (.success (.of false)) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
          unfold SpecTec.«$match_heaptype_exists:clause:0» at hfirst
          cases hfirst with
          | bind_success hg _ =>
              cases hg with
              | guard_true hbad => cases hbad
      | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse
              (SpecTec.«$match_heaptype_exists:clause:1» d (ht :: hts) dt)
              (fun _ => SpecTecExecution.firstSuccess
                [fun _ => SpecTec.«$match_heaptype_exists:clause:2»
                  d (ht :: hts) dt] ()))
            start (.success (.of false)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
              unfold SpecTec.«$match_heaptype_exists:clause:1» at hsecond
              cases hsecond with
              | bind_success _ hrest =>
                  cases hrest with
                  | bind_success _ hrest =>
                      cases hrest with
                      | bind_success _ hpure => cases hpure
          | orElse_unmatch _ htail2 =>
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (.orElse
                  (SpecTec.«$match_heaptype_exists:clause:2»
                    d (ht :: hts) dt) (fun _ => .unmatch))
                start (.success (.of false)) finalSupply at htail2
              cases htail2 with
              | orElse_success hthird =>
                  unfold SpecTec.«$match_heaptype_exists:clause:2» at hthird
                  cases hthird with
                  | bind_success hg hrest =>
                      cases hg with
                      | guard_true _ =>
                          cases hrest with
                          | bind_success hhead hrest =>
                              rename_i headResult
                              cases hrest with
                              | bind_success hnot hrest =>
                                  cases hnot with
                                  | guard_true hfalse =>
                                      cases hrest with
                                      | bind_success hrecursive hpure =>
                                          cases hpure with
                                          | pure =>
                                              cases headResult with
                                              | true =>
                                                  exact False.elim (hfalse rfl)
                                              | false =>
                                                  exact ⟨_, hhead, hrecursive⟩
              | orElse_unmatch _ hnil => cases hnil
  · rintro ⟨middle, hhead, hrecursive⟩
    exact match_heaptype_exists_cons_tail_result d ht hts dt false
      start middle finalSupply hhead hrecursive

end properties.wasm_module_not_ok.Rejection
