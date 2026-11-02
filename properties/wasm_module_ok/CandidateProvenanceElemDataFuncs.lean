import properties.wasm_module_ok.CandidateProvenancePostGlobals
import properties.wasm_module_ok.ElemDataGlobalsValidation
import properties.wasm_module_ok.LateTypesTransport
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateProvenanceElemDataFuncs

theorem elem_ok_funcs (c result : SpecTec.context)
    (e : SpecTec.elem) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Elem_ok c e⟩)
      n (.success (.of result)) finalSupply) :
    result.FUNCS = c.FUNCS := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Elem_ok_clauses c e))
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hclause =>
      unfold SpecTec.«Elem_ok:clause:0» at hclause
      cases hclause with
      | bind_success _ htail =>
        cases htail with
        | bind_success _ htail =>
          cases htail with
          | bind_success _ hpure =>
            cases hpure with
            | pure => rfl
    | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem data_ok_funcs (c result : SpecTec.context)
    (d : SpecTec.data) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Data_ok c d⟩)
      n (.success (.of result)) finalSupply) :
    result.FUNCS = c.FUNCS := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Data_ok_clauses c d))
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hclause =>
      unfold SpecTec.«Data_ok:clause:0» at hclause
      cases hclause with
      | bind_success _ hpure =>
        cases hpure with
        | pure => rfl
    | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem elems_ok_funcs (c result : SpecTec.context)
    (ts : List SpecTec.elem) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Elems_ok c ts⟩)
      n (.success (.of result)) finalSupply) :
    result.FUNCS = c.FUNCS := by
  induction ts generalizing c n finalSupply result with
  | nil =>
      cases hcall with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Elems_ok:clause:0» c [])
            (fun _ => SpecTecExecution.tryClauses
              [SpecTec.«Elems_ok:clause:1» c []]))
          n (.success (.of result)) finalSupply at hbody
        cases hbody with
        | orElse_success hfirst =>
          unfold SpecTec.«Elems_ok:clause:0» at hfirst
          cases hfirst with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond => simp at hcond
        | orElse_unmatch hfailedSupply htail =>
          restore_supply hfailedSupply at htail
          change SpecTecExecution.Eval SpecTec.Body
            (.orElse (SpecTec.«Elems_ok:clause:1» c [])
              (fun _ => .unmatch))
            n (.success (.of result)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
            unfold SpecTec.«Elems_ok:clause:1» at hsecond
            cases hsecond with
            | bind_success _ hpure =>
              cases hpure with
              | pure => rfl
          | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone
  | cons t rest ih =>
      cases hcall with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Elems_ok:clause:0» c (t :: rest))
            (fun _ => SpecTecExecution.tryClauses
              [SpecTec.«Elems_ok:clause:1» c (t :: rest)]))
          n (.success (.of result)) finalSupply at hbody
        cases hbody with
        | orElse_success hfirst =>
          unfold SpecTec.«Elems_ok:clause:0» at hfirst
          cases hfirst with
          | bind_success hguard htail =>
            cases hguard with
            | guard_true _ =>
              cases htail with
              | bind_success hhead htail =>
                rename_i middle c₁
                cases htail with
                | bind_success hrest hpure =>
                  cases hpure with
                  | pure =>
                    exact (ih c₁ result middle finalSupply hrest).trans
                      (elem_ok_funcs c c₁ t n middle hhead)
        | orElse_unmatch hfailedSupply htail =>
          restore_supply hfailedSupply at htail
          change SpecTecExecution.Eval SpecTec.Body
            (.orElse (SpecTec.«Elems_ok:clause:1» c (t :: rest))
              (fun _ => .unmatch))
            n (.success (.of result)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
            unfold SpecTec.«Elems_ok:clause:1» at hsecond
            cases hsecond with
            | bind_success hguard _ =>
              cases hguard with
              | guard_true hcond => simp at hcond
          | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem datas_ok_funcs (c result : SpecTec.context)
    (ts : List SpecTec.data) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Datas_ok c ts⟩)
      n (.success (.of result)) finalSupply) :
    result.FUNCS = c.FUNCS := by
  induction ts generalizing c n finalSupply result with
  | nil =>
      cases hcall with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Datas_ok:clause:0» c [])
            (fun _ => SpecTecExecution.tryClauses
              [SpecTec.«Datas_ok:clause:1» c []]))
          n (.success (.of result)) finalSupply at hbody
        cases hbody with
        | orElse_success hfirst =>
          unfold SpecTec.«Datas_ok:clause:0» at hfirst
          cases hfirst with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond => simp at hcond
        | orElse_unmatch hfailedSupply htail =>
          restore_supply hfailedSupply at htail
          change SpecTecExecution.Eval SpecTec.Body
            (.orElse (SpecTec.«Datas_ok:clause:1» c [])
              (fun _ => .unmatch))
            n (.success (.of result)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
            unfold SpecTec.«Datas_ok:clause:1» at hsecond
            cases hsecond with
            | bind_success _ hpure =>
              cases hpure with
              | pure => rfl
          | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone
  | cons t rest ih =>
      cases hcall with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Datas_ok:clause:0» c (t :: rest))
            (fun _ => SpecTecExecution.tryClauses
              [SpecTec.«Datas_ok:clause:1» c (t :: rest)]))
          n (.success (.of result)) finalSupply at hbody
        cases hbody with
        | orElse_success hfirst =>
          unfold SpecTec.«Datas_ok:clause:0» at hfirst
          cases hfirst with
          | bind_success hguard htail =>
            cases hguard with
            | guard_true _ =>
              cases htail with
              | bind_success hhead htail =>
                rename_i middle c₁
                cases htail with
                | bind_success hrest hpure =>
                  cases hpure with
                  | pure =>
                    exact (ih c₁ result middle finalSupply hrest).trans
                      (data_ok_funcs c c₁ t n middle hhead)
        | orElse_unmatch hfailedSupply htail =>
          restore_supply hfailedSupply at htail
          change SpecTecExecution.Eval SpecTec.Body
            (.orElse (SpecTec.«Datas_ok:clause:1» c (t :: rest))
              (fun _ => .unmatch))
            n (.success (.of result)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
            unfold SpecTec.«Datas_ok:clause:1» at hsecond
            cases hsecond with
            | bind_success hguard _ =>
              cases hguard with
              | guard_true hcond => simp at hcond
          | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone
theorem trace_elems_provenance
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m) :
    CandidateUniverseReady.Provenance tr.c7 := by
  exact CandidateProvenanceImports.of_relevant_fields_eq tr.c6 tr.c7
    (DeclarationTypesValidation.elems_ok_types
      tr.c6 tr.c7 m.ELEMS tr.n9 tr.n10 tr.elems_ok)
    (elems_ok_funcs tr.c6 tr.c7 m.ELEMS tr.n9 tr.n10 tr.elems_ok)
    (ElemDataGlobalsValidation.elems_ok_globals
      tr.c6 tr.c7 m.ELEMS tr.n9 tr.n10 tr.elems_ok)
    (CandidateProvenancePostGlobals.trace_tags_provenance m tr)

theorem trace_datas_provenance
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m) :
    CandidateUniverseReady.Provenance tr.c8 := by
  exact CandidateProvenanceImports.of_relevant_fields_eq tr.c7 tr.c8
    (DeclarationTypesValidation.datas_ok_types
      tr.c7 tr.c8 m.DATAS tr.n10 tr.n11 tr.datas_ok)
    (datas_ok_funcs tr.c7 tr.c8 m.DATAS tr.n10 tr.n11 tr.datas_ok)
    (ElemDataGlobalsValidation.datas_ok_globals
      tr.c7 tr.c8 m.DATAS tr.n10 tr.n11 tr.datas_ok)
    (trace_elems_provenance m tr)

theorem ready_of_types_eq
    (c out : SpecTec.context)
    (hTypes : out.TYPES = c.TYPES)
    (hready : CandidateTypeReady.Ready c) :
    CandidateTypeReady.Ready out := by
  constructor
  · intro p dt hlookup
    simpa [hTypes] using hready.substitution p dt
      (by simpa [hTypes] using hlookup)
  · intro p hp
    simpa [hTypes] using hready.unrolledPredecessors p
      (by simpa [hTypes] using hp)

theorem trace_final_ready
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m) :
    CandidateTypeReady.Ready tr.c8 := by
  have hvalidated : ValidatedTypeChain.ValidatedTypes tr.c0 :=
    ValidatedTypeChain.types_ok_preserves
      {tr.c with REFS := tr.free} tr.c0 m.TYPES tr.n2 tr.n3
      (CandidateTypesTraceIntegration.initial_validated m tr) tr.types_ok
  have himports :=
    ((ImportsValidation.imports_success_iff_result
      tr.c0 m.IMPORTS tr.c1 tr.n3 tr.n4).mp tr.imports_ok).1
  have hTypes : tr.c8.TYPES = tr.c0.TYPES :=
    (LateTypesTransport.trace_header_types m tr).trans
      (ContextTypesValidation.imports_types tr.c0 tr.c1 m.IMPORTS himports)
  exact ready_of_types_eq tr.c0 tr.c8 hTypes
    (CandidateTypeReady.validated_types_ready tr.c0 hvalidated)

theorem trace_candidate_val_match_iff
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (u t : SpecTec.valtype) (b : Bool) (start finish : Nat)
    (hu : u ∈ FiniteValidTypes.candidateUniverse tr.c8)
    (ht : t ∈ FiniteValidTypes.candidateUniverse tr.c8) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_valtype» tr.c8.TYPES u t⟩)
      start (.success (.of b)) finish ↔
    b = CandidateValMatch.candidateValMatch tr.c8 u t ∧ finish = start := by
  exact CandidateUniverseReady.candidate_universe_match_iff
    tr.c8 u t b start finish
    (trace_final_ready m tr)
    (trace_datas_provenance m tr) hu ht

end properties.wasm_module_ok.CandidateProvenanceElemDataFuncs
