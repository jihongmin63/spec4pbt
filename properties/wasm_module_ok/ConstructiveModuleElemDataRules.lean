import properties.wasm_module_ok.ConstructiveModuleModeRules
import properties.wasm_module_ok.EmptyStageValidation
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleElemDataRules
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyEvalReduction

theorem elems_nil (c out : context) (n finish : Nat)
    (h : Eval Body (.call ⟨context,Call.Elems_ok c []⟩) n (.success (.of out)) finish) :
    out=c ∧ finish=n := by
  obtain ⟨ho,hn⟩ := properties.wasm_module_ok.Execution.eval_deterministic h (EmptyStageValidation.elems_nil_total c n)
  exact ⟨by cases ho;rfl,hn⟩

theorem elems_cons (c next out : context) (e : SpecTec.elem) (es : List SpecTec.elem) (n middle finish : Nat)
    (hh : Eval Body (.call ⟨context,Call.Elem_ok c e⟩) n (.success (.of next)) middle)
    (ht : Eval Body (.call ⟨context,Call.Elems_ok next es⟩) middle (.success (.of out)) finish) :
    Eval Body (.call ⟨context,Call.Elems_ok c (e::es)⟩) n (.success (.of out)) finish := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.Elems_ok_clauses c (e::es))) n (.success (.of out)) finish
  apply tryClauses_cons_success
  unfold SpecTec.«Elems_ok:clause:0»
  exact Eval.bind_success (Eval.guard_true rfl) (Eval.bind_success hh (Eval.bind_success ht (Eval.pure out)))

theorem elems_original (c out : context) (e : SpecTec.elem) (es : List SpecTec.elem) (n finish : Nat)
    (h : Eval Body (.call ⟨context,Call.Elems_ok c (e::es)⟩) n (.success (.of out)) finish) :
    ∃next middle,
      Eval Body (.call ⟨context,Call.Elem_ok c e⟩) n (.success (.of next)) middle ∧
      Eval Body (.call ⟨context,Call.Elems_ok next es⟩) middle (.success (.of out)) finish := by
  cases h with | call h =>
    obtain ⟨_,hs⟩ := (tryClauses_success_iff (SpecTec.Elems_ok_clauses c (e::es)) n (.of out) finish).1 h
    cases hs with
    | here h =>
      unfold SpecTec.«Elems_ok:clause:0» at h
      obtain ⟨_,h⟩ := (bind_guard _ _ _ _ _).1 h
      cases h with | bind_success hh h =>
        cases h with | bind_success ht hp =>
          cases hp;exact ⟨_,_,hh,ht⟩
    | next _ hs => cases hs with
      | here h =>
        unfold SpecTec.«Elems_ok:clause:1» at h
        obtain ⟨hg,_⟩ := (bind_guard _ _ _ _ _).1 h
        simp at hg
      | next _ hs => cases hs

theorem datas_nil (c out : context) (n finish : Nat)
    (h : Eval Body (.call ⟨context,Call.Datas_ok c []⟩) n (.success (.of out)) finish) :
    out=c ∧ finish=n := by
  obtain ⟨ho,hn⟩ := properties.wasm_module_ok.Execution.eval_deterministic h (EmptyStageValidation.datas_nil_total c n)
  exact ⟨by cases ho;rfl,hn⟩

theorem datas_cons (c next out : context) (e : SpecTec.data) (es : List SpecTec.data) (n middle finish : Nat)
    (hh : Eval Body (.call ⟨context,Call.Data_ok c e⟩) n (.success (.of next)) middle)
    (ht : Eval Body (.call ⟨context,Call.Datas_ok next es⟩) middle (.success (.of out)) finish) :
    Eval Body (.call ⟨context,Call.Datas_ok c (e::es)⟩) n (.success (.of out)) finish := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.Datas_ok_clauses c (e::es))) n (.success (.of out)) finish
  apply tryClauses_cons_success
  unfold SpecTec.«Datas_ok:clause:0»
  exact Eval.bind_success (Eval.guard_true rfl) (Eval.bind_success hh (Eval.bind_success ht (Eval.pure out)))

theorem datas_original (c out : context) (e : SpecTec.data) (es : List SpecTec.data) (n finish : Nat)
    (h : Eval Body (.call ⟨context,Call.Datas_ok c (e::es)⟩) n (.success (.of out)) finish) :
    ∃next middle,
      Eval Body (.call ⟨context,Call.Data_ok c e⟩) n (.success (.of next)) middle ∧
      Eval Body (.call ⟨context,Call.Datas_ok next es⟩) middle (.success (.of out)) finish := by
  cases h with | call h =>
    obtain ⟨_,hs⟩ := (tryClauses_success_iff (SpecTec.Datas_ok_clauses c (e::es)) n (.of out) finish).1 h
    cases hs with
    | here h =>
      unfold SpecTec.«Datas_ok:clause:0» at h
      obtain ⟨_,h⟩ := (bind_guard _ _ _ _ _).1 h
      cases h with | bind_success hh h =>
        cases h with | bind_success ht hp =>
          cases hp;exact ⟨_,_,hh,ht⟩
    | next _ hs => cases hs with
      | here h =>
        unfold SpecTec.«Datas_ok:clause:1» at h
        obtain ⟨hg,_⟩ := (bind_guard _ _ _ _ _).1 h
        simp at hg
      | next _ hs => cases hs

theorem elem (c : context) (e : SpecTec.elem) (n : Nat)
    (hr : Eval Body (.call ⟨Unit,Call.Reftype_ok c e.ETYPE⟩) n (.success (.of ())) n)
    (hi : Eval Body (.call ⟨Unit,Call.«Elem_ok:rule:iter:0» c e.ETYPE e.EINIT⟩) n (.success (.of ())) n)
    (hm : Eval Body (.call ⟨Unit,Call.Elemmode_ok c e.ETYPE e.EMODE⟩) n (.success (.of ())) n) :
    Eval Body (.call ⟨context,Call.Elem_ok c e⟩) n (.success (.of {c with ELEMS:=c.ELEMS++[e.ETYPE]})) n := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.Elem_ok_clauses c e)) n _ n
  apply tryClauses_cons_success
  unfold SpecTec.«Elem_ok:clause:0»
  exact Eval.bind_success hr (Eval.bind_success hi (Eval.bind_success hm (Eval.pure _)))

theorem elem_original (c out : context) (e : SpecTec.elem) (n finish : Nat)
    (h : Eval Body (.call ⟨context,Call.Elem_ok c e⟩) n (.success (.of out)) finish) :
    ∃n1 n2,
      Eval Body (.call ⟨Unit,Call.Reftype_ok c e.ETYPE⟩) n (.success (.of ())) n1 ∧
      Eval Body (.call ⟨Unit,Call.«Elem_ok:rule:iter:0» c e.ETYPE e.EINIT⟩) n1 (.success (.of ())) n2 ∧
      Eval Body (.call ⟨Unit,Call.Elemmode_ok c e.ETYPE e.EMODE⟩) n2 (.success (.of ())) finish ∧
      out={c with ELEMS:=c.ELEMS++[e.ETYPE]} := by
  cases h with | call h =>
    change Eval Body (.orElse (SpecTec.«Elem_ok:clause:0» c e) (fun _ => .unmatch)) n _ finish at h
    cases h with
    | orElse_success h =>
      unfold SpecTec.«Elem_ok:clause:0» at h
      cases h with | bind_success hr h =>
        cases h with | bind_success hi h =>
          cases h with | bind_success hm hp =>
            cases hp;exact ⟨_,_,hr,hi,hm,rfl⟩
    | orElse_unmatch _ h => cases h

theorem data (c : context) (e : SpecTec.data) (n : Nat)
    (hm : Eval Body (.call ⟨Unit,Call.Datamode_ok c e.DMODE⟩) n (.success (.of ())) n) :
    Eval Body (.call ⟨context,Call.Data_ok c e⟩) n (.success (.of {c with DATAS:=c.DATAS++[datatype.OK]})) n := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.Data_ok_clauses c e)) n _ n
  apply tryClauses_cons_success
  unfold SpecTec.«Data_ok:clause:0»
  exact Eval.bind_success hm (Eval.pure _)

theorem data_original (c out : context) (e : SpecTec.data) (n finish : Nat)
    (h : Eval Body (.call ⟨context,Call.Data_ok c e⟩) n (.success (.of out)) finish) :
    Eval Body (.call ⟨Unit,Call.Datamode_ok c e.DMODE⟩) n (.success (.of ())) finish ∧
      out={c with DATAS:=c.DATAS++[datatype.OK]} := by
  cases h with | call h =>
    change Eval Body (.orElse (SpecTec.«Data_ok:clause:0» c e) (fun _ => .unmatch)) n _ finish at h
    cases h with
    | orElse_success h =>
      unfold SpecTec.«Data_ok:clause:0» at h
      cases h with | bind_success hm hp =>
        cases hp;exact ⟨hm,rfl⟩
    | orElse_unmatch _ h => cases h

#print axioms elems_original
#print axioms datas_original
#print axioms elem_original
#print axioms data_original
end properties.wasm_module_ok.ConstructiveModuleElemDataRules
