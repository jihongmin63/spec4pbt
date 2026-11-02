import properties.wasm_module_ok.ConstFillabilityDecision
import properties.wasm_module_ok.CandidateValMembership
import properties.wasm_module_ok.GlobaltypeValidation
import properties.wasm_module_ok.TabletypeValidation
import properties.wasm_module_ok.ElemDataConstValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstValidatedTarget

theorem valid_target_in_extended_and_table
    (c : SpecTec.context) (t : SpecTec.valtype)
    (hvalid : ValtypeValidation.valtypeValid c t = true) :
    t ∈ ConstFieldCandidate.extendedCandidateUniverse c ∧
      CandidateValMatch.InTableVal c t := by
  exact ⟨ConstFieldCandidate.old_candidate_mem_extended c t
      (FiniteValidTypes.valid_mem_candidateUniverse c t hvalid),
    CandidateValMembership.valid_candidate_in_table c t
      ((FiniteValidTypes.validCandidates_spec c t).2 hvalid)⟩

theorem globaltype_target_in_extended_and_table
    (c : SpecTec.context) (mutation : SpecTec.«mut»)
    (t : SpecTec.valtype) (start finish : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Globaltype_ok c (.GlobalT mutation t)⟩)
      start (.success (.of ())) finish) :
    t ∈ ConstFieldCandidate.extendedCandidateUniverse c ∧
      CandidateValMatch.InTableVal c t := by
  have hvalid := (GlobaltypeValidation.globaltype_success_iff_valid
    c (.GlobalT mutation t) start finish).1 hcall
  exact valid_target_in_extended_and_table c t hvalid.1

theorem reftype_target_in_extended_and_table
    (c : SpecTec.context) (rt : SpecTec.reftype)
    (hvalid : ReftypeTotal.reftypeValid c rt = true) :
    SpecTec.valtype.RefT rt ∈
        ConstFieldCandidate.extendedCandidateUniverse c ∧
      CandidateValMatch.InTableVal c (.RefT rt) := by
  cases rt with
  | «% %» null ht =>
    apply valid_target_in_extended_and_table
    simpa [ValtypeValidation.valtypeValid,
      ReftypeTotal.reftypeValid] using hvalid

theorem tabletype_target_in_extended_and_table
    (c : SpecTec.context) (addr : SpecTec.addrtype)
    (lim : SpecTec.limits) (rt : SpecTec.reftype)
    (start finish : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Tabletype_ok c (.TableT addr lim rt)⟩)
      start (.success (.of ())) finish) :
    SpecTec.valtype.RefT rt ∈
        ConstFieldCandidate.extendedCandidateUniverse c ∧
      CandidateValMatch.InTableVal c (.RefT rt) := by
  have hvalid := (TabletypeValidation.tabletype_success_iff_valid
    c (.TableT addr lim rt) start finish).1 hcall
  cases addr <;> cases rt with
  | «% %» null ht =>
    apply valid_target_in_extended_and_table
    · have hr : ReftypeTotal.reftypeValid c (.«% %» null ht) = true := by
        cases h : ReftypeTotal.reftypeValid c (.«% %» null ht) with
        | true => rfl
        | false => simp [TabletypeValidation.tabletypeValid, h] at hvalid
      simpa [ValtypeValidation.valtypeValid,
        ReftypeTotal.reftypeValid] using hr

theorem elem_target_in_extended_and_table
    (c result : SpecTec.context) (e : SpecTec.elem)
    (start finish : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Elem_ok c e⟩)
      start (.success (.of result)) finish) :
    SpecTec.valtype.RefT e.ETYPE ∈
        ConstFieldCandidate.extendedCandidateUniverse c ∧
      CandidateValMatch.InTableVal c (.RefT e.ETYPE) := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.Elem_ok_clauses c e) ())
      start (.success (.of result)) finish at hbody
    cases hbody with
    | orElse_success hclause =>
      unfold SpecTec.«Elem_ok:clause:0» at hclause
      cases hclause with
      | bind_success href _ =>
        have hvalid := (ReftypeTotal.reftype_success_iff_valid
          c e.ETYPE _ _).1 href
        exact reftype_target_in_extended_and_table c e.ETYPE hvalid.1
    | orElse_unmatch _ hnone => cases hnone

theorem numeric_target_in_extended_and_table
    (c : SpecTec.context) (num : SpecTec.numtype) :
    SpecTec.valtype.NumT num ∈
        ConstFieldCandidate.extendedCandidateUniverse c ∧
      CandidateValMatch.InTableVal c (.NumT num) := by
  exact valid_target_in_extended_and_table c (.NumT num) rfl

end properties.wasm_module_ok.ConstValidatedTarget
