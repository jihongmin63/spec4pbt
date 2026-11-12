import properties.wasm_module_ok.ConstructiveModuleModeRules
import properties.wasm_module_ok.ConstructiveBodyIndexedTypes
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleModes
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyEnvironment ConstructiveConstTableCore
open ConstructiveModuleInitializerPlans ConstructiveBodyIndexedTypes

abbrev DataMode (c : context) := {m : datamode // ∀n,Eval Body
  (.call ⟨Unit,Call.Datamode_ok c m⟩) n (.success (.of ())) n}
abbrev ElemMode (c : context) (rt : reftype) := {m : elemmode // ∀n,Eval Body
  (.call ⟨Unit,Call.Elemmode_ok c rt m⟩) n (.success (.of ())) n}

def passiveData (c : context) : DataMode c := ⟨.Passive,ConstructiveModuleModeRules.data_passive c⟩
def activeData (c : context) (mem : Memory c)
    (code : Constant c (.NumT (AddrNumtypeDecision.numtypeOfAddrtype mem.addr))) : DataMode c :=
  ⟨.Active ⟨mem.index,code.val⟩,fun n => ConstructiveModuleModeRules.data_active c _ mem.addr mem.lim mem.lookup n n (code.property n)⟩
def data (c : context) (env : Env c) : Audited (DataMode c) :=
  (Audited.pure (passiveData c)).merge ((memories c).map fun mem =>
    (ConstructiveModuleOffsetPlans.generate c env mem.addr).map (activeData c mem))

def passiveElem (c : context) (rt : reftype) : ElemMode c rt := ⟨.Passive,ElemModeBaseDecision.passive_total c rt⟩
def declarativeElem (c : context) (rt : reftype) : ElemMode c rt := ⟨.Declarative,ElemModeBaseDecision.declarative_total c rt⟩
def activeElem (c : context) (env : Env c) (rt : reftype)
    (hr : CandidateValMatch.InTableVal c (.RefT rt)) (tab : Table c)
    (hm : CandidateReftypeMatch.candidateReftypeMatch c rt tab.rt=true)
    (code : Constant c (.NumT (AddrNumtypeDecision.numtypeOfAddrtype tab.addr))) : ElemMode c rt :=
  ⟨.Active ⟨tab.index,code.val⟩,fun n => ConstructiveModuleModeRules.elem_active c rt _ tab.addr tab.lim tab.rt tab.lookup n n
    ((CandidateReftypeMatch.candidate_reftype_match_iff c rt tab.rt true n n env.ready hr (tab.backed env)).2 ⟨hm.symm,rfl⟩)
    (code.property n)⟩

def elemBranches (c : context) (env : Env c) (rt : reftype)
    (hr : CandidateValMatch.InTableVal c (.RefT rt)) : List (Audited (ElemMode c rt)) :=
  (tables c).flatMap fun tab =>
    if hm : CandidateReftypeMatch.candidateReftypeMatch c rt tab.rt=true then
      [(ConstructiveModuleOffsetPlans.generate c env tab.addr).map (activeElem c env rt hr tab hm)] else []
def elem (c : context) (env : Env c) (rt : reftype)
    (hr : CandidateValMatch.InTableVal c (.RefT rt)) : Audited (ElemMode c rt) :=
  (Audited.pure (passiveElem c rt)).merge (Audited.pure (declarativeElem c rt)::elemBranches c env rt hr)

theorem data_complete (c : context) (env : Env c) (mode : datamode) (n finish : Nat)
    (h : Eval Body (.call ⟨Unit,Call.Datamode_ok c mode⟩) n (.success (.of ())) finish) :
    ∃out : DataMode c,Gen.support (data c env).generator out ∧ out.val=mode := by
  cases mode with
  | Passive => exact ⟨passiveData c,(merge_support _ _ _).2 ⟨Audited.pure _,List.mem_cons_self,rfl⟩,rfl⟩
  | Active a =>
    obtain ⟨addr,lim,hx,hc⟩ := ConstructiveModuleModeRules.data_active_original c a n finish h
    let mem : Memory c := ⟨a.INDEX,addr,lim,hx⟩
    have ht : CandidateValMatch.InTableVal c (.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)) :=
      backed c (ConstructiveModuleOffsetPlans.target c addr)
    have hv := (ConstExpressionDecision.constant_expression_result_iff_const_ok_any_counters c _ a.OFFSET n finish
      env.ready env.provenance env.nested ht).2 hc |>.1
    let code : Constant c (.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)) := ⟨a.OFFSET,fun k =>
      (ConstExpressionDecision.constant_expression_result_iff_const_ok c _ a.OFFSET k env.ready env.provenance env.nested ht).1 hv⟩
    refine ⟨activeData c mem code,(merge_support _ _ _).2 ?_,by cases a;rfl⟩
    refine ⟨(ConstructiveModuleOffsetPlans.generate c env addr).map (activeData c mem),?_,?_⟩
    · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨mem,memories_complete c mem,rfl⟩)
    · exact ⟨code,ConstructiveModuleOffsetPlans.complete c env addr code,rfl⟩

theorem elem_complete (c : context) (env : Env c) (rt : reftype)
    (hr : CandidateValMatch.InTableVal c (.RefT rt)) (mode : elemmode) (n finish : Nat)
    (h : Eval Body (.call ⟨Unit,Call.Elemmode_ok c rt mode⟩) n (.success (.of ())) finish) :
    ∃out : ElemMode c rt,Gen.support (elem c env rt hr).generator out ∧ out.val=mode := by
  cases mode with
  | Passive => exact ⟨passiveElem c rt,(merge_support _ _ _).2 ⟨Audited.pure _,List.mem_cons_self,rfl⟩,rfl⟩
  | Declarative => exact ⟨declarativeElem c rt,(merge_support _ _ _).2 ⟨Audited.pure (declarativeElem c rt),by simp,rfl⟩,rfl⟩
  | Active a =>
    obtain ⟨addr,lim,tr,hx,hm,hc⟩ := ConstructiveModuleModeRules.elem_active_original c env rt hr a n finish h
    let tab : Table c := ⟨a.INDEX,addr,lim,tr,hx⟩
    have ht : CandidateValMatch.InTableVal c (.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)) :=
      backed c (ConstructiveModuleOffsetPlans.target c addr)
    have hv := (ConstExpressionDecision.constant_expression_result_iff_const_ok_any_counters c _ a.OFFSET n finish
      env.ready env.provenance env.nested ht).2 hc |>.1
    let code : Constant c (.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)) := ⟨a.OFFSET,fun k =>
      (ConstExpressionDecision.constant_expression_result_iff_const_ok c _ a.OFFSET k env.ready env.provenance env.nested ht).1 hv⟩
    refine ⟨activeElem c env rt hr tab hm code,(merge_support _ _ _).2 ?_,by cases a;rfl⟩
    refine ⟨(ConstructiveModuleOffsetPlans.generate c env addr).map (activeElem c env rt hr tab hm),?_,?_⟩
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_flatMap.mpr ⟨tab,tables_complete c tab,by simp [tab,hm]⟩
    · exact ⟨code,ConstructiveModuleOffsetPlans.complete c env addr code,rfl⟩

#print axioms data_complete
#print axioms elem_complete
end properties.wasm_module_ok.ConstructiveModuleModes
