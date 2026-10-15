import SpecTecDecl0373

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$contains» (arg0 : _root_.String) (arg1 : _root_.String) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$contains» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$is_some_» (X_T : Type) (arg0 : (_root_.Option X_T)) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_some_» X_T arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$opt_as_seq_» (X_T : Type) (arg0 : (_root_.Option X_T)) (arg1 : (_root_.List X_T)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List X_T), SpecTecCall.«$opt_as_seq_» X_T arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$exists_» (arg0 : (_root_.List _root_.Bool)) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$exists_» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$forall_» (arg0 : (_root_.List _root_.Bool)) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$forall_» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$init_» (arg0 : _root_.Nat) (arg1 : (_root_.List _root_.Nat)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$init_» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$repeat_» (X_T : Type) (arg0 : X_T) (arg1 : _root_.Nat) (arg2 : (_root_.List X_T)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List X_T), SpecTecCall.«$repeat_» X_T arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$partition_» (X : Type) (arg0 : (_root_.List X)) (arg1 : _root_.Nat) (arg2 : ((_root_.List X) × (_root_.List X))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List X) × (_root_.List X)), SpecTecCall.«$partition_» X arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$filter_» (X : Type) (arg0 : (_root_.List X)) (arg1 : (_root_.List _root_.Bool)) (arg2 : (_root_.List X)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List X), SpecTecCall.«$filter_» X arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$assoc_» (X : Type) (Y : Type) (arg0 : X) (arg1 : (_root_.List (X × Y))) (arg2 : (_root_.Option Y)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option Y), SpecTecCall.«$assoc_» X Y arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$distinct_» (K : Type) (arg0 : (_root_.List K)) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$distinct_» K arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$empty_set» (K : Type) (arg0 : (set K)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(set K), SpecTecCall.«$empty_set» K⟩) 0 (.success (.of (arg0))) finalSupply


noncomputable def «$in_set» (K_T : Type) [_root_.DecidableEq K_T] (arg0 : K_T) (arg1 : (set K_T)) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$in_set» K_T arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$sub_set» (K : Type) (arg0 : (set K)) (arg1 : (set K)) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$sub_set» K arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$eq_set» (K : Type) (arg0 : (set K)) (arg1 : (set K)) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$eq_set» K arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$empty_map» (K : Type) (V : Type) (arg0 : (map K V)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(map K V), SpecTecCall.«$empty_map» K V⟩) 0 (.success (.of (arg0))) finalSupply


noncomputable def «$dom_map:case_1:pattern-iter:0» (K_T : Type) (V_T : Type) (arg0 : (_root_.List (pair K_T V_T))) (arg1 : (_root_.List K_T)) (arg2 : (_root_.List V_T)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List K_T) × (_root_.List V_T)), SpecTecCall.«$dom_map:case_1:pattern-iter:0» K_T V_T arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$dom_map» (K_T : Type) (V_T : Type) (arg0 : (map K_T V_T)) (arg1 : (set K_T)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(set K_T), SpecTecCall.«$dom_map» K_T V_T arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$codom_map:case_1:pattern-iter:0» (K_T : Type) (V_T : Type) (arg0 : (_root_.List (pair K_T V_T))) (arg1 : (_root_.List K_T)) (arg2 : (_root_.List V_T)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List K_T) × (_root_.List V_T)), SpecTecCall.«$codom_map:case_1:pattern-iter:0» K_T V_T arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$codom_map» (K_T : Type) (V_T : Type) (arg0 : (map K_T V_T)) (arg1 : (set V_T)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(set V_T), SpecTecCall.«$codom_map» K_T V_T arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$find_map:list» (K : Type) (V : Type) (arg0 : (_root_.List (pair K V))) (arg1 : K) (arg2 : (_root_.Option V)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option V), SpecTecCall.«$find_map:list» K V arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_map» (K : Type) (V : Type) (arg0 : (map K V)) (arg1 : K) (arg2 : (_root_.Option V)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option V), SpecTecCall.«$find_map» K V arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_maps» (K : Type) (V : Type) (arg0 : (_root_.List (map K V))) (arg1 : K) (arg2 : (_root_.Option V)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option V), SpecTecCall.«$find_maps» K V arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$add_map:list» (K : Type) (V : Type) (arg0 : (_root_.List (pair K V))) (arg1 : K) (arg2 : V) (arg3 : (_root_.List (pair K V))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair K V)), SpecTecCall.«$add_map:list» K V arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$add_map» (K : Type) (V : Type) (arg0 : (map K V)) (arg1 : K) (arg2 : V) (arg3 : (map K V)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(map K V), SpecTecCall.«$add_map» K V arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$adds_map» (K : Type) (V : Type) (arg0 : (map K V)) (arg1 : (_root_.List K)) (arg2 : (_root_.List V)) (arg3 : (map K V)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(map K V), SpecTecCall.«$adds_map» K V arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$update_map:list» (K : Type) (V : Type) (arg0 : (_root_.List (pair K V))) (arg1 : K) (arg2 : V) (arg3 : (_root_.List (pair K V))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair K V)), SpecTecCall.«$update_map:list» K V arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$update_map» (K : Type) (V : Type) (arg0 : (map K V)) (arg1 : K) (arg2 : V) (arg3 : (map K V)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(map K V), SpecTecCall.«$update_map» K V arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$extend_map:case_1:pattern-iter:0» (K : Type) (V : Type) (arg0 : (_root_.List (pair K V))) (arg1 : (_root_.List K)) (arg2 : (_root_.List V)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List K) × (_root_.List V)), SpecTecCall.«$extend_map:case_1:pattern-iter:0» K V arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$extend_map:case_1:pattern-iter:2» (K : Type) (V : Type) (arg0 : (_root_.List (pair K V))) (arg1 : (_root_.List K)) (arg2 : (_root_.List V)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List K) × (_root_.List V)), SpecTecCall.«$extend_map:case_1:pattern-iter:2» K V arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$extend_map:case_1:iter:4» (K : Type) (V : Type) (arg0 : (_root_.List K)) (arg1 : (_root_.List V)) (arg2 : (_root_.List (pair K V))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair K V)), SpecTecCall.«$extend_map:case_1:iter:4» K V arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$extend_map:case_1:pattern-iter:7» (K : Type) (V : Type) (arg0 : (_root_.List (pair K V))) (arg1 : (_root_.List K)) (arg2 : (_root_.List V)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List K) × (_root_.List V)), SpecTecCall.«$extend_map:case_1:pattern-iter:7» K V arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply

end SpecTec
