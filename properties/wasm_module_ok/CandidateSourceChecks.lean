import properties.wasm_module_ok.SubtypeValidation
import properties.wasm_module_ok.CandidateRectypeTable
import properties.wasm_module_ok.RectypeSourceValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateSourceChecks

/-- The first recursive-group validation pass, before subtype matching. -/
def sourceChecks (c : SpecTec.context) : List SpecTec.subtype → Bool
  | [] => true
  | st :: sts => SubtypeValidation.subtypeValid c st && sourceChecks c sts

theorem iter5_nil_success (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.«Rectype_ok:rule:iter:5» c []⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«Rectype_ok:rule:iter:5_clauses» c []) ())
    n (.success (.of ())) n
  apply SpecTecExecution.firstSuccess_cons_success
  exact SpecTecExecution.Eval.pure ()

theorem iter5_cons_success_iff
    (c : SpecTec.context) (st : SpecTec.subtype)
    (sts : List SpecTec.subtype) (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:5» c (st :: sts)⟩)
      n (.success (.of ())) finish ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Subtype_ok c st⟩)
        n (.success (.of ())) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«Rectype_ok:rule:iter:5» c sts⟩)
        middle (.success (.of ())) finish := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      obtain ⟨idx, hselected⟩ :=
        (SpecTecExecution.firstSuccess_success_iff
          (SpecTec.«Rectype_ok:rule:iter:5_clauses» c (st :: sts)) ()
          n (.of ()) finish).1 hbody
      unfold SpecTec.«Rectype_ok:rule:iter:5_clauses» at hselected
      cases hselected with
      | here hfirst =>
          unfold SpecTec.«Rectype_ok:rule:iter:5:clause:0» at hfirst
          cases hfirst
      | next _ hrest =>
          cases hrest with
          | here hsecond =>
              unfold SpecTec.«Rectype_ok:rule:iter:5:clause:1» at hsecond
              cases hsecond with
              | bind_success hhead htailplan =>
                  rename_i middle _
                  cases htailplan with
                  | bind_success htail hpure =>
                      cases hpure
                      exact ⟨middle, hhead, htail⟩
          | next _ hnone => cases hnone
  · rintro ⟨middle, hhead, hrest⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«Rectype_ok:rule:iter:5_clauses» c (st :: sts)) ())
      n (.success (.of ())) finish
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Rectype_ok:rule:iter:5:clause:0» c (st :: sts))
        n .unmatch n
      exact SpecTecExecution.Eval.unmatch
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Rectype_ok:rule:iter:5:clause:1» c (st :: sts))
        n (.success (.of ())) finish
      unfold SpecTec.«Rectype_ok:rule:iter:5:clause:1»
      apply SpecTecExecution.Eval.bind_success hhead
      apply SpecTecExecution.Eval.bind_success hrest
      exact SpecTecExecution.Eval.pure ()

theorem iter5_success_iff_sourceChecks
    (c : SpecTec.context) (sts : List SpecTec.subtype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.«Rectype_ok:rule:iter:5» c sts⟩)
      n (.success (.of ())) finish ↔
    sourceChecks c sts = true ∧ finish = n := by
  induction sts generalizing n finish with
  | nil =>
      constructor
      · intro h
        have hdet : SpecTecExecution.PrimitiveDeterministic
            SpecTec.specTecProgram := by
          intro request x y hp
          cases hp
        obtain ⟨_, hsupply⟩ :=
          SpecTecExecution.eval_deterministic hdet h
            (iter5_nil_success c n)
        exact ⟨rfl, hsupply⟩
      · rintro ⟨_, rfl⟩
        exact iter5_nil_success c finish
  | cons st sts ih =>
      constructor
      · intro h
        obtain ⟨middle, hhead, hrest⟩ :=
          (iter5_cons_success_iff c st sts n finish).1 h
        obtain ⟨hvalid, hmiddle⟩ :=
          (SubtypeValidation.subtype_success_iff_valid
            c st n middle).1 hhead
        obtain ⟨hvalidRest, hsupply⟩ :=
          (ih middle finish).1 hrest
        subst middle
        exact ⟨by simp [sourceChecks, hvalid, hvalidRest], hsupply⟩
      · rintro ⟨hall, rfl⟩
        have hparts : SubtypeValidation.subtypeValid c st = true ∧
            sourceChecks c sts = true := by
          simpa [sourceChecks] using hall
        obtain ⟨hhead, hrest⟩ := hparts
        apply (iter5_cons_success_iff c st sts finish finish).2
        exact ⟨finish,
          (SubtypeValidation.subtype_success_iff_valid
            c st finish finish).2 ⟨hhead, rfl⟩,
          (ih finish finish).2 ⟨hrest, rfl⟩⟩

/-- Every successful recursive group passes the finite source check in the
context computed before subtype matching. -/
theorem rectype_success_sourceChecks
    (before after candidate : SpecTec.context)
    (sts : List SpecTec.subtype) (start finish : Nat)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hcandidate : CandidateRectypeTable.candidateContext before sts =
      some candidate) :
    sourceChecks candidate sts = true := by
  have hactual := CandidateRectypeTable.rectype_success_candidateContext
    before after sts start finish hrect
  have heq : candidate = after :=
    Option.some.inj (hcandidate.symm.trans hactual)
  subst candidate
  obtain ⟨dts, hafter, iterStart, iterFinish, hiter⟩ :=
    RectypeSourceValidation.rectype_ok_extract_validation_iter
      before after sts start finish hrect
  subst after
  exact ((iter5_success_iff_sourceChecks
    {before with TYPES := before.TYPES ++ dts} sts iterStart iterFinish).1
      hiter).1

end properties.wasm_module_ok.CandidateSourceChecks
