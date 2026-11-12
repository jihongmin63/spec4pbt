import properties.wasm_module_ok.RefCycleDirect
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstSyntaxValidation

theorem const_iter_cons_success_iff
    (c : SpecTec.context) (i : SpecTec.instr)
    (rest : List SpecTec.instr) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.«Const_ok:rule:iter:0» c (i :: rest)⟩)
      n (.success (.of ())) finalSupply ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$is_const» c i⟩)
        n (.success (.of true)) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.«Const_ok:rule:iter:0» c rest⟩)
        middle (.success (.of ())) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«Const_ok:rule:iter:0:clause:0» c (i :: rest))
          (fun _ => SpecTecExecution.tryClauses
            [SpecTec.«Const_ok:rule:iter:0:clause:1» c (i :: rest)]))
        n (.success (.of ())) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        unfold SpecTec.«Const_ok:rule:iter:0:clause:0» at hfirst
        cases hfirst
      | orElse_unmatch hfailedSupply htail =>
        restore_supply hfailedSupply at htail
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Const_ok:rule:iter:0:clause:1» c (i :: rest))
            (fun _ => .unmatch))
          n (.success (.of ())) finalSupply at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Const_ok:rule:iter:0:clause:1» at hsecond
          cases hsecond with
          | bind_success his htail =>
            rename_i middle isConst
            cases htail with
            | bind_success hguard htail =>
              cases hguard with
              | guard_true htrue =>
                subst htrue
                cases htail with
                | bind_success hrest hpure =>
                  cases hpure with
                  | pure => exact ⟨middle, his, hrest⟩
        | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone
  · rintro ⟨middle, his, hrest⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«Const_ok:rule:iter:0_clauses» c (i :: rest)))
      n (.success (.of ())) finalSupply
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Const_ok:rule:iter:0:clause:0» c (i :: rest))
        n .unmatch n
      unfold SpecTec.«Const_ok:rule:iter:0:clause:0»
      exact SpecTecExecution.Eval.unmatch
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Const_ok:rule:iter:0:clause:1» c (i :: rest))
      n (.success (.of ())) finalSupply
    unfold SpecTec.«Const_ok:rule:iter:0:clause:1»
    apply SpecTecExecution.Eval.bind_success his
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    apply SpecTecExecution.Eval.bind_success hrest
    exact SpecTecExecution.Eval.pure _

theorem const_iter_member_is_const
    (c : SpecTec.context) (xs : List SpecTec.instr)
    (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.«Const_ok:rule:iter:0» c xs⟩)
      n (.success (.of ())) finalSupply)
    (i : SpecTec.instr) (hmem : i ∈ xs) :
    ∃ start finish : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$is_const» c i⟩)
        start (.success (.of true)) finish := by
  induction xs generalizing n finalSupply with
  | nil => simp at hmem
  | cons head tail ih =>
      obtain ⟨middle, hhead, htail⟩ :=
        (const_iter_cons_success_iff c head tail n finalSupply).mp hcall
      rcases List.mem_cons.mp hmem with heq | htailmem
      · subst heq
        exact ⟨n, middle, hhead⟩
      · exact ih middle finalSupply htail htailmem

theorem const_ok_member_is_const
    (c : SpecTec.context) (t : SpecTec.valtype)
    (xs : SpecTec.const) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Const_ok c t xs⟩)
      n (.success (.of ())) finalSupply)
    (i : SpecTec.instr) (hmem : i ∈ xs) :
    ∃ start finish : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$is_const» c i⟩)
        start (.success (.of true)) finish := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (.orElse (SpecTec.«Const_ok:clause:0» c t xs) (fun _ => .unmatch))
      n (.success (.of ())) finalSupply at hbody
    cases hbody with
    | orElse_success hclause =>
      unfold SpecTec.«Const_ok:clause:0» at hclause
      cases hclause with
      | bind_success hiter _ =>
        exact const_iter_member_is_const c xs n _ hiter i hmem
    | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

end properties.wasm_module_ok.ConstSyntaxValidation
