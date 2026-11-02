import properties.wasm_module_ok.HeaptypeValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.SubtypeHeadListValidation

/-- The first subtype pass checks every supertype without comparing subtypes. -/
def allHeaptypesValid (c : SpecTec.context) :
    List SpecTec.heaptype → Bool
  | [] => true
  | ht :: hts => HeaptypeValidation.heaptypeValid c ht &&
      allHeaptypesValid c hts

theorem iter_nil_success (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Subtype_ok:rule:iter:0» c []⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«Subtype_ok:rule:iter:0_clauses» c []) ())
    n (.success (.of ())) n
  apply SpecTecExecution.firstSuccess_cons_success
  exact SpecTecExecution.Eval.pure ()

theorem iter_cons_success_iff
    (c : SpecTec.context) (ht : SpecTec.heaptype)
    (hts : List SpecTec.heaptype) (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Subtype_ok:rule:iter:0» c (ht :: hts)⟩)
      n (.success (.of ())) finish ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Heaptype_ok c ht⟩)
        n (.success (.of ())) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«Subtype_ok:rule:iter:0» c hts⟩)
        middle (.success (.of ())) finish := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse
          (SpecTec.«Subtype_ok:rule:iter:0:clause:0» c (ht :: hts))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ =>
              SpecTec.«Subtype_ok:rule:iter:0:clause:1» c (ht :: hts)] ()))
        n (.success (.of ())) finish at hbody
      cases hbody with
      | orElse_success hfirst =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.unmatch) n (.success (.of ())) finish at hfirst
        cases hfirst
      | orElse_unmatch _ htail =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.orElse
            (SpecTec.«Subtype_ok:rule:iter:0:clause:1» c (ht :: hts))
            (fun _ => .unmatch))
          n (.success (.of ())) finish at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Subtype_ok:rule:iter:0:clause:1» at hsecond
          cases hsecond with
          | bind_success hhead htail =>
            rename_i middle value
            cases value
            cases htail with
            | bind_success hrest hpure =>
              rename_i _ valueRest
              cases valueRest
              cases hpure
              exact ⟨middle, hhead, hrest⟩
        | orElse_unmatch _ hnone => cases hnone
  · rintro ⟨middle, hhead, hrest⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«Subtype_ok:rule:iter:0_clauses» c (ht :: hts)) ())
      n (.success (.of ())) finish
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Subtype_ok:rule:iter:0:clause:0» c (ht :: hts))
        n .unmatch n
      exact SpecTecExecution.Eval.unmatch
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Subtype_ok:rule:iter:0:clause:1» c (ht :: hts))
        n (.success (.of ())) finish
      unfold SpecTec.«Subtype_ok:rule:iter:0:clause:1»
      apply SpecTecExecution.Eval.bind_success hhead
      apply SpecTecExecution.Eval.bind_success hrest
      exact SpecTecExecution.Eval.pure ()

theorem iter_success_iff_valid
    (c : SpecTec.context) (hts : List SpecTec.heaptype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Subtype_ok:rule:iter:0» c hts⟩)
      n (.success (.of ())) finish ↔
    allHeaptypesValid c hts = true ∧ finish = n := by
  induction hts generalizing n finish with
  | nil =>
    constructor
    · intro h
      have hdet : SpecTecExecution.PrimitiveDeterministic
          SpecTec.specTecProgram := by
        intro request x y hp
        cases hp
      obtain ⟨_, hsupply⟩ :=
        SpecTecExecution.eval_deterministic hdet h
          (iter_nil_success c n)
      exact ⟨rfl, hsupply⟩
    · rintro ⟨_, rfl⟩
      exact iter_nil_success c finish
  | cons ht hts ih =>
    constructor
    · intro h
      obtain ⟨middle, hhead, hrest⟩ :=
        (iter_cons_success_iff c ht hts n finish).1 h
      obtain ⟨hvalid, hmiddle⟩ :=
        (HeaptypeValidation.heaptype_success_iff_valid
          c ht n middle).1 hhead
      obtain ⟨hvalidRest, hsupply⟩ :=
        (ih middle finish).1 hrest
      subst middle
      exact ⟨by simp [allHeaptypesValid, hvalid, hvalidRest], hsupply⟩
    · rintro ⟨hall, rfl⟩
      have hparts : HeaptypeValidation.heaptypeValid c ht = true ∧
          allHeaptypesValid c hts = true := by
        simpa [allHeaptypesValid] using hall
      obtain ⟨hhead, hrest⟩ := hparts
      apply (iter_cons_success_iff c ht hts finish finish).2
      exact ⟨finish,
        (HeaptypeValidation.heaptype_success_iff_valid
          c ht finish finish).2 ⟨hhead, rfl⟩,
        (ih finish finish).2 ⟨hrest, rfl⟩⟩

end properties.wasm_module_ok.SubtypeHeadListValidation
