import properties.wasm_module_ok.CandidateGroupSuperIter
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateGroupSuperChecks

/-- The index list and subtype list are consumed together, exactly as in the
translated closing iterator. -/
def pairedChecks (c : SpecTec.context) (base : Nat) :
    List Nat → List SpecTec.subtype → Bool
  | [], [] => true
  | i :: is, .SubT _ hts strt :: sts =>
      CandidateStaticSuperList.staticSuperChecks c (base + i) strt hts &&
        pairedChecks c base is sts
  | _, _ => false

theorem iter6_success_iff_pairedChecks
    (c : SpecTec.context) (base : Nat)
    (ns : List Nat) (sts : List SpecTec.subtype)
    (n finish : Nat)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (hready : CandidateTypeReady.Ready c) :
    CandidateSourceChecks.sourceChecks c sts = true →
    ns.length = sts.length →
    (SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Rectype_ok:rule:iter:6» c base ns sts⟩)
      n (.success (.of ())) finish ↔
      pairedChecks c base ns sts = true ∧ finish = n) := by
  induction ns generalizing sts n finish with
  | nil =>
      cases sts with
      | nil =>
          intro _ _
          constructor
          · intro h
            obtain ⟨_, hsupply⟩ :=
              properties.wasm_module_ok.Execution.eval_deterministic h
                (CandidateGroupSuperIter.iter6_nil_success c base n)
            exact ⟨rfl, hsupply⟩
          · rintro ⟨_, rfl⟩
            exact CandidateGroupSuperIter.iter6_nil_success c base finish
      | cons st sts =>
          intro _ hlen
          simp at hlen
  | cons i is ih =>
      cases sts with
      | nil =>
          intro _ hlen
          simp at hlen
      | cons st sts =>
          cases st with
          | SubT fin hts strt =>
              intro hsource hlen
              have hparts :
                  SubtypeValidation.subtypeValid c (.SubT fin hts strt) = true ∧
                  CandidateSourceChecks.sourceChecks c sts = true := by
                simpa [CandidateSourceChecks.sourceChecks] using hsource
              have hlenTail : is.length = sts.length := by
                simpa using hlen
              have hsub : SpecTecExecution.Eval SpecTec.Body
                  (.call ⟨Unit,
                    SpecTec.Call.Subtype_ok c (.SubT fin hts strt)⟩)
                  n (.success (.of ())) n :=
                (SubtypeValidation.subtype_success_iff_valid
                  c (.SubT fin hts strt) n n).2 ⟨hparts.1, rfl⟩
              constructor
              · intro h
                obtain ⟨middle, hhead, hrest⟩ :=
                  (CandidateGroupSuperIter.iter6_cons_success_iff
                    c base i is (.SubT fin hts strt) sts n finish).1 h
                obtain ⟨hcheck, hmiddle⟩ :=
                  (CandidateStaticSuperList.subtype_sub_success_iff_checks
                    c (base + i) fin hts strt
                    n n n middle hsub hnested hready).1 hhead
                obtain ⟨hchecks, hsupply⟩ :=
                  (ih sts middle finish hparts.2 hlenTail).1 hrest
                subst middle
                exact ⟨by simp [pairedChecks, hcheck, hchecks], hsupply⟩
              · rintro ⟨hall, rfl⟩
                have hchecks :
                    CandidateStaticSuperList.staticSuperChecks
                      c (base + i) strt hts = true ∧
                    pairedChecks c base is sts = true := by
                  simpa [pairedChecks] using hall
                apply (CandidateGroupSuperIter.iter6_cons_success_iff
                  c base i is (.SubT fin hts strt) sts finish finish).2
                have hsub' : SpecTecExecution.Eval SpecTec.Body
                    (.call ⟨Unit,
                      SpecTec.Call.Subtype_ok c
                        (.SubT fin hts strt)⟩)
                    finish (.success (.of ())) finish :=
                  (SubtypeValidation.subtype_success_iff_valid
                    c (.SubT fin hts strt) finish finish).2
                    ⟨hparts.1, rfl⟩
                exact ⟨finish,
                  (CandidateStaticSuperList.subtype_sub_success_iff_checks
                    c (base + i) fin hts strt
                    finish finish finish finish hsub' hnested hready).2
                    ⟨hchecks.1, rfl⟩,
                  (ih sts finish finish hparts.2 hlenTail).2
                    ⟨hchecks.2, rfl⟩⟩

end properties.wasm_module_ok.CandidateGroupSuperChecks
