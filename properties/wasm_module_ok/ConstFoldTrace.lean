import properties.wasm_module_ok.ConstFoldDecision
import properties.wasm_module_ok.InstrsValidation
import properties.wasm_module_ok.ConstExtendedCandidateReady
import properties.wasm_module_ok.ConstCandidateTableMembership
import properties.wasm_module_ok.StackClosure

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstFoldTrace

/-- The cons clause of translated `Instrs_ok` is exactly one successful
constant stack step followed by the remaining instruction list. -/
theorem constant_instrs_cons_iff
    (c : SpecTec.context) (available : List SpecTec.valtype)
    (i : SpecTec.instr) (rest : List SpecTec.instr)
    (result : SpecTec.inferresulttype × List SpecTec.idx)
    (start finish : Nat)
    (hallowed : ConstSyntaxDecision.syntaxAllowed c i = true)
    (hready : CandidateTypeReady.Ready c)
    (havailable : ∀ t ∈ available,
      CandidateValMatch.InTableVal c t)
    (hinputs : ∀ iit need,
      ConstInstrDecision.constantInstructionResult c
        (.NoEllipses, available) i = some iit →
      iit.1.INS = (.NoEllipses, need) →
      ∀ t ∈ need, CandidateValMatch.InTableVal c t) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
        SpecTec.Call.Instrs_ok c
          (.NoEllipses, available) (i :: rest)⟩)
      start (.success (.of result)) finish ↔
    ∃ next : List SpecTec.valtype,
      ConstStepDecision.constantStepResult c available i =
        some (.NoEllipses, next) ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
          SpecTec.Call.Instrs_ok c
            (.NoEllipses, next) rest⟩)
        start (.success (.of result)) finish := by
  constructor
  · intro hwhole
    obtain ⟨iit, c₁, popped, pushed,
      middle₁, middle₂, middle₃, middle₄,
      hinstr, hinit, hpop, hpush, htail⟩ :=
      (InstrsValidation.instrs_cons_success_iff
        c (.NoEllipses, available) i rest result start finish).1 hwhole
    obtain ⟨hi, _⟩ :=
      (ConstInstrDecision.constant_instruction_result_iff
        c (.NoEllipses, available) i iit start middle₁).2
        ⟨hallowed, hinstr⟩
    have hlocals : iit.2 = [] :=
      (ConstInstrDecision.constant_instruction_input_shape
        c (.NoEllipses, available) i iit hi).choose_spec.2
    have hc₁ : c₁ = c := by
      have hcomputed :=
        ((LocalInitValidation.init_locals_success_iff_result
          c iit.2 c₁ middle₁ middle₂).1 hinit).1
      simpa [hlocals, LocalInitValidation.initLocalsResult]
        using hcomputed.symm
    subst c₁
    have hcalls : ConstStepDecision.StepCalls c available i pushed
        start middle₁ middle₂ middle₃ middle₄ :=
      ⟨hallowed, iit, popped, hinstr, hinit, hpop, hpush⟩
    obtain ⟨hstep, _, _, _, hm₄⟩ :=
      (ConstStepDecision.constant_step_calls_any_counters
        c available i pushed start middle₁ middle₂ middle₃ middle₄
        hready havailable hinputs).1 hcalls
    obtain ⟨next, hshape⟩ :=
      ConstStepDecision.constant_step_result_concrete_stack
        c available i pushed hstep
    subst pushed
    exact ⟨next, hstep, by simpa only [hm₄] using htail⟩
  · rintro ⟨next, hstep, htail⟩
    have hcalls :=
      (ConstStepDecision.constant_step_calls_any_counters
        c available i (.NoEllipses, next)
        start start start start start
        hready havailable hinputs).2
        ⟨hstep, rfl, rfl, rfl, rfl⟩
    obtain ⟨_, iit, popped, hinstr, hinit, hpop, hpush⟩ := hcalls
    exact (InstrsValidation.instrs_cons_success_iff
      c (.NoEllipses, available) i rest result start finish).2
      ⟨iit, c, popped, (.NoEllipses, next),
        start, start, start, start,
        hinstr, hinit, hpop, hpush, htail⟩

def RequiredInTable (c : SpecTec.context)
    (available : List SpecTec.valtype) (i : SpecTec.instr) : Prop :=
  ∀ iit need,
    ConstInstrDecision.constantInstructionResult c
      (.NoEllipses, available) i = some iit →
    iit.1.INS = (.NoEllipses, need) →
    ∀ t ∈ need, CandidateValMatch.InTableVal c t

/-- The table-membership conditions needed at every stack reached by the
constant fold.  It constrains only successful next states. -/
inductive FoldAdmissible (c : SpecTec.context) :
    List SpecTec.valtype → List SpecTec.instr → Prop where
  | nil (available : List SpecTec.valtype)
      (havailable : ∀ t ∈ available,
        CandidateValMatch.InTableVal c t) :
      FoldAdmissible c available []
  | cons (available : List SpecTec.valtype)
      (i : SpecTec.instr) (rest : List SpecTec.instr)
      (havailable : ∀ t ∈ available,
        CandidateValMatch.InTableVal c t)
      (hinputs : RequiredInTable c available i)
      (hnext : ∀ next,
        ConstStepDecision.constantStepResult c available i =
          some (.NoEllipses, next) →
        FoldAdmissible c next rest) :
      FoldAdmissible c available (i :: rest)

theorem constant_fold_result_iff_instrs_ok
    (c : SpecTec.context) (available : List SpecTec.valtype)
    (xs : List SpecTec.instr) (final : SpecTec.inferresulttype)
    (n : Nat) (hready : CandidateTypeReady.Ready c)
    (hadmissible : FoldAdmissible c available xs) :
    ConstFoldDecision.constantFoldResult c available xs = some final ↔
      (∀ i ∈ xs, ConstSyntaxDecision.syntaxAllowed c i = true) ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
          SpecTec.Call.Instrs_ok c
            (.NoEllipses, available) xs⟩)
        n (.success (.of (final, ([] : List SpecTec.idx)))) n := by
  induction xs generalizing available final with
  | nil =>
      constructor
      · intro hfold
        have hfinal : final = (.NoEllipses, available) := by
          simpa [ConstFoldDecision.constantFoldResult] using hfold.symm
        subst final
        constructor
        · intro i hi
          cases hi
        · exact InstrsValidation.instrs_nil_total
            c (.NoEllipses, available) n
      · rintro ⟨_, hcall⟩
        have hresult :=
          ((InstrsValidation.instrs_nil_success_iff
            c (.NoEllipses, available)
            (final, ([] : List SpecTec.idx)) n n).1 hcall).1
        have hfinal : final = (.NoEllipses, available) :=
          congrArg Prod.fst hresult
        simp [ConstFoldDecision.constantFoldResult, hfinal]
  | cons i rest ih =>
      cases hadmissible with
      | cons _ _ _ havailable hinputs hnext =>
          constructor
          · intro hfold
            obtain ⟨next, hstep, htail⟩ :=
              (ConstFoldDecision.constant_fold_cons_iff
                c available i rest final).1 hfold
            have hallowed :=
              ConstFoldDecision.constant_fold_success_all_allowed
                c available (i :: rest) final hfold
            have hhead : ConstSyntaxDecision.syntaxAllowed c i = true :=
              hallowed i (by simp)
            have htailCall :=
              ((ih next final (hnext next hstep)).1 htail).2
            exact ⟨hallowed,
              (constant_instrs_cons_iff c available i rest
                (final, ([] : List SpecTec.idx)) n n
                hhead hready havailable hinputs).2
                ⟨next, hstep, htailCall⟩⟩
          · rintro ⟨hallowed, hcall⟩
            have hhead : ConstSyntaxDecision.syntaxAllowed c i = true :=
              hallowed i (by simp)
            obtain ⟨next, hstep, htailCall⟩ :=
              (constant_instrs_cons_iff c available i rest
                (final, ([] : List SpecTec.idx)) n n
                hhead hready havailable hinputs).1 hcall
            have hrestAllowed : ∀ j ∈ rest,
                ConstSyntaxDecision.syntaxAllowed c j = true := by
              intro j hj
              exact hallowed j (by simp [hj])
            have htail :=
              (ih next final (hnext next hstep)).2
                ⟨hrestAllowed, htailCall⟩
            exact (ConstFoldDecision.constant_fold_cons_iff
              c available i rest final).2 ⟨next, hstep, htail⟩

theorem fold_admissible_of_provenance
    (c : SpecTec.context) (xs : List SpecTec.instr)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (available : List SpecTec.valtype)
    (havailable : ∀ t ∈ available,
      CandidateValMatch.InTableVal c t) :
    FoldAdmissible c available xs := by
  induction xs generalizing available with
  | nil => exact .nil available havailable
  | cons i rest ih =>
      have hinputs : RequiredInTable c available i := by
        intro iit need hi hins
        obtain ⟨hallowed, hcall⟩ :=
          (ConstInstrDecision.constant_instruction_result_iff
            c (.NoEllipses, available) i iit 0 0).1 ⟨hi, rfl⟩
        have hconst :=
          ConstAdditionalSyntaxValidation.syntax_is_const c i 0
            ((ConstSyntaxDecision.syntaxAllowed_iff c i).1 hallowed)
        have hrequired :=
          ConstExtendedCandidateReady.is_const_instruction_inputs_in_table
            c (.NoEllipses, available) i iit 0 0 0
            hconst hcall hprov hnested
        intro t ht
        exact hrequired t (by simpa only [hins] using ht)
      apply FoldAdmissible.cons available i rest havailable hinputs
      intro next hstep
      obtain ⟨hallowed, iit, popped, hcall, _, hpop, hpush⟩ :=
        (ConstStepDecision.constant_step_result_iff_calls
          c available i (.NoEllipses, next) 0 hready
          havailable hinputs).1 hstep
      obtain ⟨need, hins, _⟩ :=
        ConstInstrDecision.constant_instruction_input_shape
          c (.NoEllipses, available) i iit
          ((ConstInstrDecision.constant_instruction_result_iff
            c (.NoEllipses, available) i iit 0 0).2
            ⟨hallowed, hcall⟩).1
      obtain ⟨u, houts⟩ :=
        ConstSyntaxSingleton.syntax_instruction_singleton_outputs
          c (.NoEllipses, available) i iit 0 0
          ((ConstSyntaxDecision.syntaxAllowed_iff c i).1 hallowed) hcall
      have hpop' : SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.inferresulttype,
            SpecTec.Call.«$pop» c
              (.NoEllipses, need) (.NoEllipses, available)⟩)
          0 (.success (.of popped)) 0 := by
        simpa only [hins] using hpop
      have hpush' : SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.inferresulttype,
            SpecTec.Call.«$push» c
              (.NoEllipses, [u]) popped⟩)
          0 (.success (.of
            ((.NoEllipses, next) : SpecTec.inferresulttype))) 0 := by
        simpa only [houts] using hpush
      have houtTable :=
        ConstCandidateTableMembership.constant_instruction_outputs_in_table
          c (.NoEllipses, available) i iit 0 0
          ((ConstSyntaxDecision.syntaxAllowed_iff c i).1 hallowed)
          hcall hprov
      have hnextTable : ∀ t ∈ next,
          CandidateValMatch.InTableVal c t := by
        have hclosed := StackClosure.pop_push_entries_closed
          c need [u] available popped (.NoEllipses, next)
          0 0 0 hpop' hpush'
          (CandidateValMatch.InTableVal c) havailable
          (by
            intro t ht
            exact houtTable t (by simpa only [houts] using ht))
        exact hclosed
      exact ih next hnextTable

theorem constant_fold_empty_stack_iff_instrs_ok
    (c : SpecTec.context) (xs : List SpecTec.instr)
    (final : SpecTec.inferresulttype) (n : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true) :
    ConstFoldDecision.constantFoldResult c [] xs = some final ↔
      (∀ i ∈ xs, ConstSyntaxDecision.syntaxAllowed c i = true) ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
          SpecTec.Call.Instrs_ok c (.NoEllipses, []) xs⟩)
        n (.success (.of (final, ([] : List SpecTec.idx)))) n := by
  exact constant_fold_result_iff_instrs_ok c [] xs final n hready
    (fold_admissible_of_provenance c xs hready hprov hnested []
      (by intro t ht; cases ht))

theorem constant_instrs_trace_normalize
    (c : SpecTec.context) (available : List SpecTec.valtype)
    (xs : List SpecTec.instr)
    (result : SpecTec.inferresulttype × List SpecTec.idx)
    (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hadmissible : FoldAdmissible c available xs)
    (hallowed : ∀ i ∈ xs,
      ConstSyntaxDecision.syntaxAllowed c i = true)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
        SpecTec.Call.Instrs_ok c
          (.NoEllipses, available) xs⟩)
      start (.success (.of result)) finish) :
    ∃ final : SpecTec.inferresulttype,
      ConstFoldDecision.constantFoldResult c available xs = some final ∧
      result = (final, ([] : List SpecTec.idx)) ∧
      finish = start := by
  induction xs generalizing available result start finish with
  | nil =>
      obtain ⟨hresult, hfinish⟩ :=
        (InstrsValidation.instrs_nil_success_iff
          c (.NoEllipses, available) result start finish).1 hcall
      exact ⟨(.NoEllipses, available), rfl, hresult, hfinish⟩
  | cons i rest ih =>
      cases hadmissible with
      | cons _ _ _ havailable hinputs hnext =>
          have hhead : ConstSyntaxDecision.syntaxAllowed c i = true :=
            hallowed i (by simp)
          obtain ⟨next, hstep, htail⟩ :=
            (constant_instrs_cons_iff c available i rest result
              start finish hhead hready havailable hinputs).1 hcall
          have hrestAllowed : ∀ j ∈ rest,
              ConstSyntaxDecision.syntaxAllowed c j = true := by
            intro j hj
            exact hallowed j (by simp [hj])
          obtain ⟨final, hfoldTail, hresult, hfinish⟩ :=
            ih next result start finish (hnext next hstep)
              hrestAllowed htail
          exact ⟨final,
            (ConstFoldDecision.constant_fold_cons_iff
              c available i rest final).2
              ⟨next, hstep, hfoldTail⟩,
            hresult, hfinish⟩

theorem constant_fold_result_entries_in_table
    (c : SpecTec.context) (available : List SpecTec.valtype)
    (xs : List SpecTec.instr) (final : SpecTec.inferresulttype)
    (hadmissible : FoldAdmissible c available xs)
    (hfold : ConstFoldDecision.constantFoldResult c available xs =
      some final) :
    ∀ t ∈ final.2, CandidateValMatch.InTableVal c t := by
  induction xs generalizing available with
  | nil =>
      cases hadmissible with
      | nil _ havailable =>
          have hfinal : final = (.NoEllipses, available) := by
            simpa [ConstFoldDecision.constantFoldResult] using hfold.symm
          simpa [hfinal] using havailable
  | cons i rest ih =>
      cases hadmissible with
      | cons _ _ _ _ _ hnext =>
          obtain ⟨next, hstep, htail⟩ :=
            (ConstFoldDecision.constant_fold_cons_iff
              c available i rest final).1 hfold
          exact ih next (hnext next hstep) htail

end properties.wasm_module_ok.ConstFoldTrace
