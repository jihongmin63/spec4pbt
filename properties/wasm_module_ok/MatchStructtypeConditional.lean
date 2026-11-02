import properties.wasm_module_ok.MatchFieldConditional

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchStructtypeConditional

def allFieldsMatched
    (fieldMatch : SpecTec.fieldtype → SpecTec.fieldtype → Bool) :
    List SpecTec.fieldtype → List SpecTec.fieldtype → Bool
  | [], [] => true
  | a :: as, b :: bs => fieldMatch a b && allFieldsMatched fieldMatch as bs
  | _, _ => false

def structMatch
    (fieldMatch : SpecTec.fieldtype → SpecTec.fieldtype → Bool)
    (a b : SpecTec.structtype) : Bool :=
  match a, b with
  | .StructT as, .StructT bs =>
      decide (bs.length ≤ as.length) &&
        allFieldsMatched fieldMatch (as.take bs.length) bs

theorem iter_nil_total (dts : List SpecTec.deftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«$match_structtype:case_1:iter:0»
          dts [] []⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_structtype:case_1:iter:0_clauses»
        dts [] []) ())
    n (.success (.of ())) n
  apply SpecTecExecution.firstSuccess_cons_success
  exact SpecTecExecution.Eval.pure ()

theorem iter_cons_success_iff
    (dts : List SpecTec.deftype)
    (a b : SpecTec.fieldtype)
    (as bs : List SpecTec.fieldtype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«$match_structtype:case_1:iter:0»
          dts (a :: as) (b :: bs)⟩)
      n (.success (.of ())) finish ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_fieldtype» dts a b⟩)
        n (.success (.of true)) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«$match_structtype:case_1:iter:0»
            dts as bs⟩)
        middle (.success (.of ())) finish := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      obtain ⟨idx, hselected⟩ :=
        (SpecTecExecution.firstSuccess_success_iff
          (SpecTec.«$match_structtype:case_1:iter:0_clauses»
            dts (a :: as) (b :: bs)) ()
          n (.of ()) finish).1 hbody
      unfold SpecTec.«$match_structtype:case_1:iter:0_clauses» at hselected
      cases hselected with
      | here hfirst =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.unmatch) n (.success (.of ())) finish at hfirst
        cases hfirst
      | next _ hrest =>
        cases hrest with
        | here hsecond =>
          unfold SpecTec.«$match_structtype:case_1:iter:0:clause:1» at hsecond
          cases hsecond with
          | bind_success hfield htail =>
            rename_i middle matched
            cases htail with
            | bind_success hguard htail =>
              cases hguard with
              | guard_true htrue =>
                cases htrue
                cases htail with
                | bind_success hiter hpure =>
                  cases hpure
                  exact ⟨middle, hfield, hiter⟩
        | next _ hnone => cases hnone
  · rintro ⟨middle, hfield, hiter⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$match_structtype:case_1:iter:0_clauses»
          dts (a :: as) (b :: bs)) ())
      n (.success (.of ())) finish
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_structtype:case_1:iter:0:clause:0»
          dts (a :: as) (b :: bs)) n .unmatch n
      exact SpecTecExecution.Eval.unmatch
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_structtype:case_1:iter:0:clause:1»
          dts (a :: as) (b :: bs))
        n (.success (.of ())) finish
      unfold SpecTec.«$match_structtype:case_1:iter:0:clause:1»
      apply SpecTecExecution.Eval.bind_success hfield
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success hiter
        exact SpecTecExecution.Eval.pure ()

theorem iter_success_iff_allFieldsMatched_of_field
    (dts : List SpecTec.deftype)
    (fieldMatch : SpecTec.fieldtype → SpecTec.fieldtype → Bool)
    (hfield : ∀ a b n,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_fieldtype» dts a b⟩)
        n (.success (.of (fieldMatch a b))) n)
    (as bs : List SpecTec.fieldtype)
    (hlen : as.length = bs.length)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«$match_structtype:case_1:iter:0»
          dts as bs⟩)
      n (.success (.of ())) finish ↔
    allFieldsMatched fieldMatch as bs = true ∧ finish = n := by
  induction as generalizing bs n finish with
  | nil =>
    cases bs with
    | nil =>
      constructor
      · intro h
        have hdet : SpecTecExecution.PrimitiveDeterministic
            SpecTec.specTecProgram := by
          intro request x y hp
          cases hp
        obtain ⟨_, hsupply⟩ :=
          SpecTecExecution.eval_deterministic hdet h
            (iter_nil_total dts n)
        exact ⟨rfl, hsupply⟩
      · rintro ⟨_, rfl⟩
        exact iter_nil_total dts finish
    | cons b bs =>
      simp at hlen
  | cons a as ih =>
    cases bs with
    | nil =>
      simp at hlen
    | cons b bs =>
      have hlenTail : as.length = bs.length := by
        simpa using hlen
      constructor
      · intro h
        obtain ⟨middle, hhead, htail⟩ :=
          (iter_cons_success_iff dts a b as bs n finish).1 h
        have hdet : SpecTecExecution.PrimitiveDeterministic
            SpecTec.specTecProgram := by
          intro request x y hp
          cases hp
        obtain ⟨hresult, hmiddle⟩ :=
          SpecTecExecution.eval_deterministic hdet hhead
            (hfield a b n)
        have hvalid : fieldMatch a b = true := by
          cases hv : fieldMatch a b with
          | false => simp [hv] at hresult
          | true => rfl
        obtain ⟨hrest, hsupply⟩ :=
          (ih bs hlenTail middle finish).1 htail
        subst middle
        exact ⟨by simp [allFieldsMatched, hvalid, hrest], hsupply⟩
      · rintro ⟨hall, rfl⟩
        have hparts : fieldMatch a b = true ∧
            allFieldsMatched fieldMatch as bs = true := by
          simpa [allFieldsMatched] using hall
        apply (iter_cons_success_iff
          dts a b as bs finish finish).2
        exact ⟨finish,
          by simpa [hparts.1] using hfield a b finish,
          (ih bs hlenTail finish finish).2 ⟨hparts.2, rfl⟩⟩

theorem iter_unmatch_of_false
    (dts : List SpecTec.deftype)
    (fieldMatch : SpecTec.fieldtype → SpecTec.fieldtype → Bool)
    (hfield : ∀ a b n,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_fieldtype» dts a b⟩)
        n (.success (.of (fieldMatch a b))) n)
    (as bs : List SpecTec.fieldtype)
    (hlen : as.length = bs.length)
    (hfalse : allFieldsMatched fieldMatch as bs = false)
    (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«$match_structtype:case_1:iter:0»
          dts as bs⟩)
      n .unmatch n := by
  induction as generalizing bs n with
  | nil =>
    cases bs with
    | nil => simp [allFieldsMatched] at hfalse
    | cons b bs => simp at hlen
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hlenTail : as.length = bs.length := by
        simpa using hlen
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$match_structtype:case_1:iter:0_clauses»
            dts (a :: as) (b :: bs)) ())
        n .unmatch n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_structtype:case_1:iter:0:clause:0»
            dts (a :: as) (b :: bs)) n .unmatch n
        exact SpecTecExecution.Eval.unmatch
      · apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$match_structtype:case_1:iter:0:clause:1»
              dts (a :: as) (b :: bs)) n .unmatch n
          unfold SpecTec.«$match_structtype:case_1:iter:0:clause:1»
          cases hv : fieldMatch a b with
          | false =>
            apply SpecTecExecution.Eval.bind_success
              (by simpa [hv] using hfield a b n)
            apply SpecTecExecution.Eval.bind_unmatch
            exact SpecTecExecution.Eval.guard_false (by decide)
          | true =>
            have htailFalse : allFieldsMatched fieldMatch as bs = false := by
              simpa [allFieldsMatched, hv] using hfalse
            apply SpecTecExecution.Eval.bind_success
              (by simpa [hv] using hfield a b n)
            apply SpecTecExecution.Eval.bind_success
            · exact SpecTecExecution.Eval.guard_true rfl
            · exact SpecTecExecution.Eval.bind_unmatch
                (ih bs hlenTail htailFalse n)
        · exact SpecTecExecution.firstSuccess_nil () n

theorem match_structtype_true_of_iter
    (dts : List SpecTec.deftype)
    (as bs : List SpecTec.fieldtype)
    (hwidth : bs.length ≤ as.length)
    (n finish : Nat)
    (hiter : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«$match_structtype:case_1:iter:0»
          dts (as.take bs.length) bs⟩)
      n (.success (.of ())) finish) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_structtype»
          dts (.StructT as) (.StructT bs)⟩)
      n (.success (.of true)) finish := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_structtype_clauses»
        dts (.StructT as) (.StructT bs)) ())
    n (.success (.of true)) finish
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_structtype:clause:0»
      dts (.StructT as) (.StructT bs))
    n (.success (.of true)) finish
  unfold SpecTec.«$match_structtype:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true hwidth
  · apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.orElse_success
        (SpecTecExecution.Eval.guard_true (by simpa using hwidth))
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true (by
          simpa [List.length_take, Nat.min_eq_left hwidth] using
            (show bs.length = bs.length from rfl))
      · apply SpecTecExecution.Eval.bind_success
        · simpa using hiter
        · exact SpecTecExecution.Eval.pure true

theorem match_structtype_true_iff_iter
    (dts : List SpecTec.deftype)
    (as bs : List SpecTec.fieldtype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_structtype»
          dts (.StructT as) (.StructT bs)⟩)
      n (.success (.of true)) finish ↔
    bs.length ≤ as.length ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«$match_structtype:case_1:iter:0»
            dts (as.take bs.length) bs⟩)
        n (.success (.of ())) finish := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      obtain ⟨idx, hselected⟩ :=
        (SpecTecExecution.firstSuccess_success_iff
          (SpecTec.«$match_structtype_clauses»
            dts (.StructT as) (.StructT bs)) ()
          n (.of true) finish).1 hbody
      unfold SpecTec.«$match_structtype_clauses» at hselected
      cases hselected with
      | here hfirst =>
        unfold SpecTec.«$match_structtype:clause:0» at hfirst
        cases hfirst with
        | bind_success hguard htail =>
          cases hguard with
          | guard_true hwidth =>
            cases htail with
            | bind_success hrequire htail =>
              have hdet : SpecTecExecution.PrimitiveDeterministic
                  SpecTec.specTecProgram := by
                intro request x y hp
                cases hp
              obtain ⟨_, hrequireSupply⟩ :=
                SpecTecExecution.eval_deterministic hdet hrequire
                  (SpecTecExecution.Eval.orElse_success
                    (SpecTecExecution.Eval.guard_true
                      (by simpa using hwidth)))
              cases htail with
              | bind_success hlength htail =>
                cases hlength with
                | guard_true hprefix =>
                  cases htail with
                  | bind_success hiter hpure =>
                    cases hpure
                    rename_i iterValue
                    cases iterValue
                    exact ⟨hwidth, by simpa [hrequireSupply] using hiter⟩
      | next _ hrest =>
        cases hrest with
        | here hsecond =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.pure false) n (.success (.of true)) finish at hsecond
          cases hsecond
        | next _ hnone => cases hnone
  · rintro ⟨hwidth, hiter⟩
    exact match_structtype_true_of_iter dts as bs hwidth n finish hiter

theorem match_structtype_false_of_width_fail
    (dts : List SpecTec.deftype)
    (as bs : List SpecTec.fieldtype)
    (hwidth : ¬ bs.length ≤ as.length)
    (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_structtype»
          dts (.StructT as) (.StructT bs)⟩)
      n (.success (.of false)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_structtype_clauses»
        dts (.StructT as) (.StructT bs)) ())
    n (.success (.of false)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_structtype:clause:0»
        dts (.StructT as) (.StructT bs)) n .unmatch n
    unfold SpecTec.«$match_structtype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false hwidth)
  · apply SpecTecExecution.firstSuccess_cons_success
    exact SpecTecExecution.Eval.pure false

theorem match_structtype_false_of_iter_unmatch
    (dts : List SpecTec.deftype)
    (as bs : List SpecTec.fieldtype)
    (hwidth : bs.length ≤ as.length)
    (n : Nat)
    (hiter : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«$match_structtype:case_1:iter:0»
          dts (as.take bs.length) bs⟩)
      n .unmatch n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_structtype»
          dts (.StructT as) (.StructT bs)⟩)
      n (.success (.of false)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_structtype_clauses»
        dts (.StructT as) (.StructT bs)) ())
    n (.success (.of false)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_structtype:clause:0»
        dts (.StructT as) (.StructT bs)) n .unmatch n
    unfold SpecTec.«$match_structtype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true hwidth
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.orElse_success
          (SpecTecExecution.Eval.guard_true (by simpa using hwidth))
      · apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true (by
            simpa [List.length_take, Nat.min_eq_left hwidth] using
              (show bs.length = bs.length from rfl))
        · exact SpecTecExecution.Eval.bind_unmatch (by simpa using hiter)
  · apply SpecTecExecution.firstSuccess_cons_success
    exact SpecTecExecution.Eval.pure false

theorem match_structtype_total_of_field
    (dts : List SpecTec.deftype)
    (fieldMatch : SpecTec.fieldtype → SpecTec.fieldtype → Bool)
    (hfield : ∀ a b n,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_fieldtype» dts a b⟩)
        n (.success (.of (fieldMatch a b))) n)
    (as bs : List SpecTec.fieldtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_structtype»
          dts (.StructT as) (.StructT bs)⟩)
      n (.success (.of
        (structMatch fieldMatch (.StructT as) (.StructT bs)))) n := by
  by_cases hwidth : bs.length ≤ as.length
  · have hlen : (as.take bs.length).length = bs.length := by
      simp [List.length_take, Nat.min_eq_left hwidth]
    cases hall : allFieldsMatched fieldMatch (as.take bs.length) bs with
    | true =>
      have hresult : structMatch fieldMatch (.StructT as) (.StructT bs) = true := by
        simp [structMatch, hwidth, hall]
      rw [hresult]
      apply match_structtype_true_of_iter dts as bs hwidth n n
      exact (iter_success_iff_allFieldsMatched_of_field
        dts fieldMatch hfield (as.take bs.length) bs hlen n n).2
          ⟨hall, rfl⟩
    | false =>
      have hresult : structMatch fieldMatch (.StructT as) (.StructT bs) = false := by
        simp [structMatch, hwidth, hall]
      rw [hresult]
      exact match_structtype_false_of_iter_unmatch dts as bs hwidth n
        (iter_unmatch_of_false dts fieldMatch hfield
          (as.take bs.length) bs hlen hall n)
  · have hresult : structMatch fieldMatch (.StructT as) (.StructT bs) = false := by
      simp [structMatch, hwidth]
    rw [hresult]
    exact match_structtype_false_of_width_fail dts as bs hwidth n

theorem match_structtype_success_iff_of_field
    (dts : List SpecTec.deftype)
    (fieldMatch : SpecTec.fieldtype → SpecTec.fieldtype → Bool)
    (hfield : ∀ a b n,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_fieldtype» dts a b⟩)
        n (.success (.of (fieldMatch a b))) n)
    (as bs : List SpecTec.fieldtype)
    (result : Bool) (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_structtype»
          dts (.StructT as) (.StructT bs)⟩)
      n (.success (.of result)) finish ↔
    result = structMatch fieldMatch (.StructT as) (.StructT bs) ∧
      finish = n := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic
        SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet h
        (match_structtype_total_of_field
          dts fieldMatch hfield as bs n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact match_structtype_total_of_field
      dts fieldMatch hfield as bs finish

theorem match_structtype_total_of_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (a b : SpecTec.structtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_structtype» dts a b⟩)
      n (.success (.of
        (structMatch (MatchFieldConditional.fieldMatch heapMatch) a b))) n := by
  cases a with
  | StructT as =>
    cases b with
    | StructT bs =>
      exact match_structtype_total_of_field dts
        (MatchFieldConditional.fieldMatch heapMatch)
        (MatchFieldConditional.match_field_total_of_heap dts heapMatch hheap)
        as bs n

theorem match_structtype_success_iff_of_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (a b : SpecTec.structtype) (result : Bool) (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_structtype» dts a b⟩)
      n (.success (.of result)) finish ↔
    result = structMatch (MatchFieldConditional.fieldMatch heapMatch) a b ∧
      finish = n := by
  cases a with
  | StructT as =>
    cases b with
    | StructT bs =>
      exact match_structtype_success_iff_of_field dts
        (MatchFieldConditional.fieldMatch heapMatch)
        (MatchFieldConditional.match_field_total_of_heap dts heapMatch hheap)
        as bs result n finish

end properties.wasm_module_ok.MatchStructtypeConditional
