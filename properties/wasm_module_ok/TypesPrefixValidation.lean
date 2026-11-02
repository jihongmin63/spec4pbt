import properties.wasm_module_ok.RectypeRangeValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.TypesPrefixValidation

theorem type_ok_types_prefix
    (c result : SpecTec.context) (t : SpecTec.type)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Type_ok c t⟩)
      start (.success (.of result)) finish) :
    ∃ dts : List SpecTec.deftype,
      result.TYPES = c.TYPES ++ dts := by
  cases t with
  | RecT sts =>
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.Type_ok_clauses c (.RecT sts)))
        start (.success (.of result)) finish at hbody
      obtain ⟨idx, hselected⟩ :=
        (properties.wasm_module_ok.Execution.tryClauses_success_iff
          (SpecTec.Type_ok_clauses c (.RecT sts))
          start (.of result) finish).1 hbody
      unfold SpecTec.Type_ok_clauses at hselected
      cases hselected with
      | here h0 =>
          unfold SpecTec.«Type_ok:clause:0» at h0
          cases h0 with
          | bind_success hrect hpure =>
              cases hpure
              obtain ⟨dts, hc, before, after, hiter⟩ :=
                properties.wasm_module_ok.MatchHeaptypeBasic.rectype_ok_extract_range_and_sub_iter
                  c result sts _ _ hrect
              exact ⟨dts, congrArg SpecTec.context.TYPES hc⟩
      | next _ hrest => cases hrest

theorem type_ok_rectype_trace
    (c result : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Type_ok c (.RecT sts)⟩)
      start (.success (.of result)) finish) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of result)) finish := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Type_ok_clauses c (.RecT sts)))
      start (.success (.of result)) finish at hbody
    obtain ⟨idx, hselected⟩ :=
      (properties.wasm_module_ok.Execution.tryClauses_success_iff
        (SpecTec.Type_ok_clauses c (.RecT sts))
        start (.of result) finish).1 hbody
    unfold SpecTec.Type_ok_clauses at hselected
    cases hselected with
    | here h0 =>
        unfold SpecTec.«Type_ok:clause:0» at h0
        cases h0 with
        | bind_success hrect hpure =>
            cases hpure
            exact hrect
    | next _ hrest => cases hrest

theorem types_ok_types_prefix
    (c result : SpecTec.context) (ts : List SpecTec.type)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Types_ok c ts⟩)
      start (.success (.of result)) finish) :
    ∃ dts : List SpecTec.deftype,
      result.TYPES = c.TYPES ++ dts := by
  induction ts generalizing c result start finish with
  | nil =>
      cases h with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Types_ok:clause:0» c [])
            (fun _ => SpecTecExecution.tryClauses
              [SpecTec.«Types_ok:clause:1» c []]))
          start (.success (.of result)) finish at hbody
        cases hbody with
        | orElse_success hfirst =>
          unfold SpecTec.«Types_ok:clause:0» at hfirst
          cases hfirst with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond => simp at hcond
        | orElse_unmatch hfailedSupply htail =>
          restore_supply hfailedSupply at htail
          change SpecTecExecution.Eval SpecTec.Body
            (.orElse (SpecTec.«Types_ok:clause:1» c [])
              (fun _ => .unmatch))
            start (.success (.of result)) finish at htail
          cases htail with
          | orElse_success hsecond =>
            unfold SpecTec.«Types_ok:clause:1» at hsecond
            cases hsecond with
            | bind_success _ hpure =>
              cases hpure with
              | pure => exact ⟨[], by simp⟩
          | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone
  | cons t rest ih =>
      cases h with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Types_ok:clause:0» c (t :: rest))
            (fun _ => SpecTecExecution.tryClauses
              [SpecTec.«Types_ok:clause:1» c (t :: rest)]))
          start (.success (.of result)) finish at hbody
        cases hbody with
        | orElse_success hfirst =>
          unfold SpecTec.«Types_ok:clause:0» at hfirst
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
                    obtain ⟨head, hheadprefix⟩ :=
                      type_ok_types_prefix c c₁ t start middle hhead
                    obtain ⟨tail, htailprefix⟩ :=
                      ih c₁ result middle finish hrest
                    exact ⟨head ++ tail, by rw [htailprefix, hheadprefix, List.append_assoc]⟩
        | orElse_unmatch hfailedSupply htail =>
          restore_supply hfailedSupply at htail
          change SpecTecExecution.Eval SpecTec.Body
            (.orElse (SpecTec.«Types_ok:clause:1» c (t :: rest))
              (fun _ => .unmatch))
            start (.success (.of result)) finish at htail
          cases htail with
          | orElse_success hsecond =>
            unfold SpecTec.«Types_ok:clause:1» at hsecond
            cases hsecond with
            | bind_success hguard _ =>
              cases hguard with
              | guard_true hcond => simp at hcond
          | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem types_ok_cons_trace
    (c result : SpecTec.context)
    (t : SpecTec.type) (ts : List SpecTec.type)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Types_ok c (t :: ts)⟩)
      start (.success (.of result)) finish) :
    ∃ middle : Nat, ∃ next : SpecTec.context,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.context, SpecTec.Call.Type_ok c t⟩)
        start (.success (.of next)) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.context, SpecTec.Call.Types_ok next ts⟩)
        middle (.success (.of result)) finish := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (.orElse (SpecTec.«Types_ok:clause:0» c (t :: ts))
        (fun _ => SpecTecExecution.tryClauses
          [SpecTec.«Types_ok:clause:1» c (t :: ts)]))
      start (.success (.of result)) finish at hbody
    cases hbody with
    | orElse_success hfirst =>
      unfold SpecTec.«Types_ok:clause:0» at hfirst
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
              | pure => exact ⟨middle, next, hhead, hrest⟩
    | orElse_unmatch hfailedSupply htail =>
      restore_supply hfailedSupply at htail
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«Types_ok:clause:1» c (t :: ts))
          (fun _ => .unmatch))
        start (.success (.of result)) finish at htail
      cases htail with
      | orElse_success hsecond =>
        unfold SpecTec.«Types_ok:clause:1» at hsecond
        cases hsecond with
        | bind_success hguard _ =>
          cases hguard with
          | guard_true hcond => simp at hcond
      | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

end properties.wasm_module_ok.TypesPrefixValidation
