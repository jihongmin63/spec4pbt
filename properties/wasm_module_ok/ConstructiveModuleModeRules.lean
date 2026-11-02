import properties.wasm_module_ok.ConstructiveModuleOffsetPlans
import properties.wasm_module_ok.ConstructiveBodyEvalReduction
import properties.wasm_module_ok.ElemModeBaseDecision
import properties.wasm_module_ok.CandidateReftypeMatch
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleModeRules
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyEnvironment ConstructiveBodyEvalReduction

theorem data_passive (c : context) (n : Nat) : Eval Body
    (.call ⟨Unit,Call.Datamode_ok c .Passive⟩) n (.success (.of ())) n := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.Datamode_ok_clauses c .Passive)) n (.success (.of ())) n
  apply tryClauses_cons_success
  unfold SpecTec.«Datamode_ok:clause:0»
  exact Eval.bind_success (Eval.guard_true rfl) (Eval.pure ())

theorem data_active (c : context) (a : active) (addr : addrtype) (lim : limits)
    (hx : c.MEMS[a.INDEX]?=some (.MemoryT addr lim)) (n finish : Nat)
    (hc : Eval Body (.call ⟨Unit,Call.Const_ok c
      (.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)) a.OFFSET⟩) n (.success (.of ())) finish) :
    Eval Body (.call ⟨Unit,Call.Datamode_ok c (.Active a)⟩) n (.success (.of ())) finish := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.Datamode_ok_clauses c (.Active a))) n (.success (.of ())) finish
  apply tryClauses_cons_unmatch
  · unfold SpecTec.«Datamode_ok:clause:0»
    exact Eval.bind_unmatch (Eval.guard_false (by simp [SpecTec.«exec:match:datamode:Passive»,SpecTec.«exec:match:elemmode:Passive»]))
  apply tryClauses_cons_success
  unfold SpecTec.«Datamode_ok:clause:1»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total addr n)
  exact Eval.bind_success hc (Eval.pure ())

theorem data_active_original (c : context) (a : active) (n finish : Nat)
    (h : Eval Body (.call ⟨Unit,Call.Datamode_ok c (.Active a)⟩)
      n (.success (.of ())) finish) :
    ∃addr lim,c.MEMS[a.INDEX]?=some (.MemoryT addr lim) ∧
      Eval Body (.call ⟨Unit,Call.Const_ok c
        (.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)) a.OFFSET⟩) n (.success (.of ())) finish := by
  cases h with | call h =>
    obtain ⟨_,hs⟩ := (tryClauses_success_iff (SpecTec.Datamode_ok_clauses c (.Active a)) n (.of ()) finish).1 h
    cases hs with
    | here h =>
      unfold SpecTec.«Datamode_ok:clause:0» at h
      obtain ⟨hg,_⟩ := (bind_guard _ _ _ _ _).1 h
      cases hg
    | next _ hs => cases hs with
      | here h =>
        unfold SpecTec.«Datamode_ok:clause:1» at h
        obtain ⟨_,h⟩ := (bind_guard _ _ _ _ _).1 h
        obtain ⟨_,h⟩ := (bind_guard _ _ _ _ _).1 h
        cases hx : c.MEMS[a.INDEX]? with
        | none => rw [hx] at h;cases h
        | some mt =>
          rw [hx] at h
          cases mt with | MemoryT addr lim =>
            rw [bind_known _ _ _ _ _ _ (AddrNumtypeDecision.numtype_of_addrtype_total addr n)] at h
            cases h with | bind_success hc hp =>
              cases hp
              exact ⟨addr,lim,rfl,hc⟩
      | next _ hs => cases hs

theorem elem_active (c : context) (rt : reftype) (a : active) (addr : addrtype) (lim : limits) (tableRt : reftype)
    (hx : c.TABLES[a.INDEX]?=some (.TableT addr lim tableRt)) (n finish : Nat)
    (hm : Eval Body (.call ⟨Bool,Call.«$match_reftype» c.TYPES rt tableRt⟩) n (.success (.of true)) n)
    (hc : Eval Body (.call ⟨Unit,Call.Const_ok c
      (.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)) a.OFFSET⟩) n (.success (.of ())) finish) :
    Eval Body (.call ⟨Unit,Call.Elemmode_ok c rt (.Active a)⟩) n (.success (.of ())) finish := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.Elemmode_ok_clauses c rt (.Active a))) n (.success (.of ())) finish
  apply tryClauses_cons_unmatch
  · unfold SpecTec.«Elemmode_ok:clause:0»
    exact Eval.bind_unmatch (Eval.guard_false (by simp [SpecTec.«exec:match:datamode:Passive»,SpecTec.«exec:match:elemmode:Passive»]))
  apply tryClauses_cons_success
  unfold SpecTec.«Elemmode_ok:clause:1»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply Eval.bind_success hm
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (AddrNumtypeDecision.numtype_of_addrtype_total addr n)
  exact Eval.bind_success hc (Eval.pure ())

theorem elem_active_original (c : context) (env : Env c) (rt : reftype)
    (hr : CandidateValMatch.InTableVal c (.RefT rt)) (a : active) (n finish : Nat)
    (h : Eval Body (.call ⟨Unit,Call.Elemmode_ok c rt (.Active a)⟩)
      n (.success (.of ())) finish) :
    ∃addr lim tableRt,c.TABLES[a.INDEX]?=some (.TableT addr lim tableRt) ∧
      CandidateReftypeMatch.candidateReftypeMatch c rt tableRt=true ∧
      Eval Body (.call ⟨Unit,Call.Const_ok c
        (.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)) a.OFFSET⟩) n (.success (.of ())) finish := by
  cases h with | call h =>
    obtain ⟨_,hs⟩ := (tryClauses_success_iff (SpecTec.Elemmode_ok_clauses c rt (.Active a)) n (.of ()) finish).1 h
    cases hs with
    | here h =>
      unfold SpecTec.«Elemmode_ok:clause:0» at h
      obtain ⟨hg,_⟩ := (bind_guard _ _ _ _ _).1 h
      cases hg
    | next _ hs => cases hs with
      | here h =>
        unfold SpecTec.«Elemmode_ok:clause:1» at h
        obtain ⟨_,h⟩ := (bind_guard _ _ _ _ _).1 h
        obtain ⟨_,h⟩ := (bind_guard _ _ _ _ _).1 h
        cases hx : c.TABLES[a.INDEX]? with
        | none => rw [hx] at h;cases h
        | some tt =>
          rw [hx] at h
          cases tt with | TableT addr lim tr =>
            rw [bind_known _ _ _ _ _ _ (CandidateReftypeMatch.candidate_reftype_match_total c rt tr n env.ready hr
              (env.tables addr lim tr (List.mem_of_getElem? hx)))] at h
            obtain ⟨hm,h⟩ := (bind_guard _ _ _ _ _).1 h
            rw [bind_known _ _ _ _ _ _ (AddrNumtypeDecision.numtype_of_addrtype_total addr n)] at h
            cases h with | bind_success hc hp =>
              cases hp
              exact ⟨addr,lim,tr,rfl,hm,hc⟩
      | next _ hs => cases hs with
        | here h =>
          unfold SpecTec.«Elemmode_ok:clause:2» at h
          obtain ⟨hg,_⟩ := (bind_guard _ _ _ _ _).1 h
          cases hg
        | next _ hs => cases hs

#print axioms elem_active_original
#print axioms data_active_original
end properties.wasm_module_ok.ConstructiveModuleModeRules
