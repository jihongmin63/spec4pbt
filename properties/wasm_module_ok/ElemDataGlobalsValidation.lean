import properties.wasm_module_ok.TagGlobalsValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ElemDataGlobalsValidation

theorem elem_ok_globals (c result : SpecTec.context)
    (e : SpecTec.elem) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Elem_ok c e⟩)
      n (.success (.of result)) finalSupply) :
    result.GLOBALS = c.GLOBALS := by
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
    | orElse_unmatch _ hnone => cases hnone

theorem data_ok_globals (c result : SpecTec.context)
    (d : SpecTec.data) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Data_ok c d⟩)
      n (.success (.of result)) finalSupply) :
    result.GLOBALS = c.GLOBALS := by
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
    | orElse_unmatch _ hnone => cases hnone

theorem elems_ok_globals (c result : SpecTec.context)
    (ts : List SpecTec.elem) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Elems_ok c ts⟩)
      n (.success (.of result)) finalSupply) :
    result.GLOBALS = c.GLOBALS := by
  induction ts generalizing c n finalSupply result with
  | nil =>
      cases hcall with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Elems_ok:clause:0» c [])
            (fun _ => SpecTecExecution.tryClauses
              [fun _ => SpecTec.«Elems_ok:clause:1» c []]))
          n (.success (.of result)) finalSupply at hbody
        cases hbody with
        | orElse_success hfirst =>
          unfold SpecTec.«Elems_ok:clause:0» at hfirst
          cases hfirst with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond => simp at hcond
        | orElse_unmatch _ htail =>
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
          | orElse_unmatch _ hnone => cases hnone
  | cons t rest ih =>
      cases hcall with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Elems_ok:clause:0» c (t :: rest))
            (fun _ => SpecTecExecution.tryClauses
              [fun _ => SpecTec.«Elems_ok:clause:1» c (t :: rest)]))
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
                      (elem_ok_globals c c₁ t n middle hhead)
        | orElse_unmatch _ htail =>
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
          | orElse_unmatch _ hnone => cases hnone

theorem datas_ok_globals (c result : SpecTec.context)
    (ts : List SpecTec.data) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Datas_ok c ts⟩)
      n (.success (.of result)) finalSupply) :
    result.GLOBALS = c.GLOBALS := by
  induction ts generalizing c n finalSupply result with
  | nil =>
      cases hcall with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Datas_ok:clause:0» c [])
            (fun _ => SpecTecExecution.tryClauses
              [fun _ => SpecTec.«Datas_ok:clause:1» c []]))
          n (.success (.of result)) finalSupply at hbody
        cases hbody with
        | orElse_success hfirst =>
          unfold SpecTec.«Datas_ok:clause:0» at hfirst
          cases hfirst with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond => simp at hcond
        | orElse_unmatch _ htail =>
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
          | orElse_unmatch _ hnone => cases hnone
  | cons t rest ih =>
      cases hcall with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Datas_ok:clause:0» c (t :: rest))
            (fun _ => SpecTecExecution.tryClauses
              [fun _ => SpecTec.«Datas_ok:clause:1» c (t :: rest)]))
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
                      (data_ok_globals c c₁ t n middle hhead)
        | orElse_unmatch _ htail =>
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
          | orElse_unmatch _ hnone => cases hnone

theorem elems_success_no_bot_candidate
    (c out : SpecTec.context) (es : List SpecTec.elem)
    (start fin : Nat)
    (hinput : SpecTec.valtype.BotT ∉
      FiniteValidTypes.candidateUniverse c)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Elems_ok c es⟩)
      start (.success (.of out)) fin) :
    SpecTec.valtype.BotT ∉
      FiniteValidTypes.candidateUniverse out := by
  intro hb
  obtain ⟨mutation, hm⟩ :=
    (ConstCandidateBot.bot_mem_candidate_iff out).1 hb
  rw [elems_ok_globals c out es start fin h] at hm
  exact hinput
    ((ConstCandidateBot.bot_mem_candidate_iff c).2 ⟨mutation, hm⟩)

theorem datas_success_no_bot_candidate
    (c out : SpecTec.context) (ds : List SpecTec.data)
    (start fin : Nat)
    (hinput : SpecTec.valtype.BotT ∉
      FiniteValidTypes.candidateUniverse c)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Datas_ok c ds⟩)
      start (.success (.of out)) fin) :
    SpecTec.valtype.BotT ∉
      FiniteValidTypes.candidateUniverse out := by
  intro hb
  obtain ⟨mutation, hm⟩ :=
    (ConstCandidateBot.bot_mem_candidate_iff out).1 hb
  rw [datas_ok_globals c out ds start fin h] at hm
  exact hinput
    ((ConstCandidateBot.bot_mem_candidate_iff c).2 ⟨mutation, hm⟩)

end properties.wasm_module_ok.ElemDataGlobalsValidation
