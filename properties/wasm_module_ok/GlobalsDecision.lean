import properties.wasm_module_ok.GlobalDecision
import properties.wasm_module_ok.CandidateProvenanceGlobals
import properties.wasm_module_ok.CandidateProvenanceElemDataFuncs
import properties.wasm_module_ok.ConstTraceNestedReady
import properties.wasm_module_ok.EmptyStageValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.GlobalsDecision

def globalsResult (c : SpecTec.context) :
    List SpecTec.global → Option SpecTec.context
  | [] => some c
  | g :: rest =>
      (GlobalDecision.globalResult c g).bind fun next =>
        globalsResult next rest

theorem global_result_next_invariants
    (c next : SpecTec.context) (g : SpecTec.global)
    (hresult : GlobalDecision.globalResult c g = some next)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true) :
    CandidateTypeReady.Ready next ∧
      CandidateUniverseReady.Provenance next ∧
      CandidateNestedReady.nestedTableReady next = true := by
  have hout := (GlobalDecision.global_result_iff_valid c next g).1 hresult |>.2
  have htypes : next.TYPES = c.TYPES := by
    rw [hout]
  have hcall := (GlobalDecision.global_result_iff_call
    c next g 0 0 hready hprov hnested).1 ⟨hresult, rfl⟩
  exact ⟨CandidateProvenanceElemDataFuncs.ready_of_types_eq
      c next htypes hready,
    CandidateProvenanceGlobals.global_ok_provenance
      c next g 0 0 hprov hcall,
    (ConstTraceNestedReady.nested_table_ready_of_types_eq
      next c htypes).trans hnested⟩

theorem globals_nil_success_iff
    (c out : SpecTec.context) (start finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Globals_ok c []⟩)
      start (.success (.of out)) finish ↔
    c = out ∧ finish = start := by
  constructor
  · intro hcall
    have hdet : SpecTecExecution.PrimitiveDeterministic
        SpecTec.specTecProgram := by
      intro request a b hp
      cases hp
    obtain ⟨hout, hfinish⟩ :=
      SpecTecExecution.eval_deterministic hdet hcall
        (EmptyStageValidation.globals_nil_total c start)
    exact ⟨by cases hout; rfl, hfinish⟩
  · rintro ⟨hout, hfinish⟩
    subst out
    subst finish
    exact EmptyStageValidation.globals_nil_total c start

theorem globals_cons_success_iff
    (c out : SpecTec.context) (g : SpecTec.global)
    (rest : List SpecTec.global) (start finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Globals_ok c (g :: rest)⟩)
      start (.success (.of out)) finish ↔
    ∃ next : SpecTec.context, ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Global_ok c g⟩)
        start (.success (.of next)) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Globals_ok next rest⟩)
        middle (.success (.of out)) finish := by
  constructor
  · intro hcall
    cases hcall with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.Globals_ok_clauses c (g :: rest)) ())
        start (.success (.of out)) finish at hbody
      cases hbody with
      | orElse_success hfirst =>
        unfold SpecTec.«Globals_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hguard htail =>
          cases hguard with
          | guard_true _ =>
            cases htail with
            | bind_success hhead htail =>
              rename_i middle next
              cases htail with
              | bind_success hrest hpure =>
                cases hpure with
                | pure => exact ⟨next, middle, hhead, hrest⟩
      | orElse_unmatch _ htail =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«Globals_ok:clause:1» c (g :: rest)] ())
          start (.success (.of out)) finish at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Globals_ok:clause:1» at hsecond
          cases hsecond with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond => simp at hcond
        | orElse_unmatch _ hnone => cases hnone
  · rintro ⟨next, middle, hhead, hrest⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.Globals_ok_clauses c (g :: rest)) ())
      start (.success (.of out)) finish
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Globals_ok:clause:0» c (g :: rest))
      start (.success (.of out)) finish
    unfold SpecTec.«Globals_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by simp)
    apply SpecTecExecution.Eval.bind_success hhead
    apply SpecTecExecution.Eval.bind_success hrest
    exact SpecTecExecution.Eval.pure out

theorem globals_result_iff_call
    (c out : SpecTec.context) (gs : List SpecTec.global)
    (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true) :
    globalsResult c gs = some out ∧ finish = start ↔
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Globals_ok c gs⟩)
        start (.success (.of out)) finish := by
  induction gs generalizing c out start finish with
  | nil =>
    simpa [globalsResult] using
      (globals_nil_success_iff c out start finish).symm
  | cons g rest ih =>
    constructor
    · rintro ⟨hresult, hfinish⟩
      cases hhead : GlobalDecision.globalResult c g with
      | none => simp [globalsResult, hhead] at hresult
      | some next =>
        have htail : globalsResult next rest = some out := by
          simpa [globalsResult, hhead] using hresult
        obtain ⟨hreadyNext, hprovNext, hnestedNext⟩ :=
          global_result_next_invariants c next g hhead
            hready hprov hnested
        subst finish
        apply (globals_cons_success_iff c out g rest start start).2
        refine ⟨next, start, ?_, ?_⟩
        · exact (GlobalDecision.global_result_iff_call c next g
            start start hready hprov hnested).1 ⟨hhead, rfl⟩
        · exact (ih next out start start
            hreadyNext hprovNext hnestedNext).1 ⟨htail, rfl⟩
    · intro hcall
      obtain ⟨next, middle, hhead, htail⟩ :=
        (globals_cons_success_iff c out g rest start finish).1 hcall
      obtain ⟨hheadResult, hmiddle⟩ :=
        (GlobalDecision.global_result_iff_call c next g
          start middle hready hprov hnested).2 hhead
      obtain ⟨hreadyNext, hprovNext, hnestedNext⟩ :=
        global_result_next_invariants c next g hheadResult
          hready hprov hnested
      obtain ⟨htailResult, hfinish⟩ :=
        (ih next out middle finish
          hreadyNext hprovNext hnestedNext).2 htail
      exact ⟨by simpa [globalsResult, hheadResult] using htailResult,
        hfinish.trans hmiddle⟩

end properties.wasm_module_ok.GlobalsDecision
