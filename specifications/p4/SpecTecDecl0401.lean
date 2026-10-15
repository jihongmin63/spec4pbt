import SpecTecDecl0400

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$add_object_e» (arg0 : arch) (arg1 : objectId) (arg2 : object) (arg3 : arch) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨arch, SpecTecCall.«$add_object_e» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$find_archState_e» (arg0 : arch) (arg1 : archState) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨archState, SpecTecCall.«$find_archState_e» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$find_object_e» (arg0 : arch) (arg1 : objectId) (arg2 : (_root_.Option object)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option object), SpecTecCall.«$find_object_e» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_object_qualified_e» (arg0 : arch) (arg1 : objectId) (arg2 : (_root_.Option object)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option object), SpecTecCall.«$find_object_qualified_e» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$find_object_unqualified_e:case_1:pattern-iter:0» (arg0 : (_root_.List (pair (_root_.List _root_.String) object))) (arg1 : (_root_.List object)) (arg2 : (_root_.List objectId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List object) × (_root_.List objectId)), SpecTecCall.«$find_object_unqualified_e:case_1:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$find_object_unqualified_e:case_1:iter:2» (arg0 : id) (arg1 : (_root_.List object)) (arg2 : (_root_.List objectId)) (arg3 : (_root_.List (_root_.Option object))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option object)), SpecTecCall.«$find_object_unqualified_e:case_1:iter:2» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$find_object_unqualified_e:case_1:iter:5» (arg0 : (_root_.List (_root_.Option object))) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$find_object_unqualified_e:case_1:iter:5» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$find_object_unqualified_e» (arg0 : arch) (arg1 : id) (arg2 : (_root_.Option object)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option object), SpecTecCall.«$find_object_unqualified_e» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$update_archState_e» (arg0 : arch) (arg1 : archState) (arg2 : arch) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨arch, SpecTecCall.«$update_archState_e» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$update_object_qualified_e» (arg0 : arch) (arg1 : objectId) (arg2 : object) (arg3 : arch) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨arch, SpecTecCall.«$update_object_qualified_e» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$update_object_unqualified_e:case_1:pattern-iter:0» (arg0 : (_root_.List (pair (_root_.List _root_.String) object))) (arg1 : (_root_.List object)) (arg2 : (_root_.List objectId)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List object) × (_root_.List objectId)), SpecTecCall.«$update_object_unqualified_e:case_1:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «$update_object_unqualified_e:case_1:iter:2» (arg0 : id) (arg1 : (_root_.List objectId)) (arg2 : (_root_.List (_root_.Option objectId))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option objectId)), SpecTecCall.«$update_object_unqualified_e:case_1:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$update_object_unqualified_e:case_1:iter:5» (arg0 : (_root_.List (_root_.Option objectId))) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$update_object_unqualified_e:case_1:iter:5» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$update_object_unqualified_e» (arg0 : arch) (arg1 : id) (arg2 : object) (arg3 : arch) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨arch, SpecTecCall.«$update_object_unqualified_e» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Expr_eval:non-default-abort_2:pattern-iter:1» (arg0 : (_root_.List namedExpressionIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List typedExpressionIR)), SpecTecCall.«Expr_eval:non-default-abort_2:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_eval:non-default-cont_2:pattern-iter:1» (arg0 : (_root_.List namedExpressionIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List typedExpressionIR)), SpecTecCall.«Expr_eval:non-default-cont_2:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_eval:non-default-cont_2:iter:4» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«Expr_eval:non-default-cont_2:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_eval:default-abort_2:pattern-iter:1» (arg0 : (_root_.List namedExpressionIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List typedExpressionIR)), SpecTecCall.«Expr_eval:default-abort_2:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_eval:default-cont_2:pattern-iter:1» (arg0 : (_root_.List namedExpressionIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List typedExpressionIR)), SpecTecCall.«Expr_eval:default-cont_2:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_eval:default-cont_2:iter:4» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«Expr_eval:default-cont_2:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_eval:serenum:pattern-iter:5» (arg0 : (_root_.List valueFieldIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Expr_eval:serenum:pattern-iter:5» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_eval:serenum:iter:7» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (_root_.String × value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_eval:serenum:iter:7» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_eval:struct:pattern-iter:4» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List id)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«Expr_eval:struct:pattern-iter:4» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_eval:struct:iter:6» (arg0 : (_root_.List id)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (_root_.String × value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_eval:struct:iter:6» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_eval:header:pattern-iter:4» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List id)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«Expr_eval:header:pattern-iter:4» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_eval:header:iter:6» (arg0 : (_root_.List id)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (_root_.String × value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_eval:header:iter:6» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Expr_eval:headerunion:pattern-iter:4» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List id)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«Expr_eval:headerunion:pattern-iter:4» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Expr_eval:headerunion:iter:6» (arg0 : (_root_.List id)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (_root_.String × value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Expr_eval:headerunion:iter:6» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Lvalue_read:struct:pattern-iter:1» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Lvalue_read:struct:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Lvalue_read:struct:iter:3» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (_root_.String × value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Lvalue_read:struct:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Lvalue_read:header:pattern-iter:1» (arg0 : (_root_.List fieldValue)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Lvalue_read:header:pattern-iter:1» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Lvalue_read:header:iter:3» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List (_root_.String × value))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Lvalue_read:header:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

end SpecTec
