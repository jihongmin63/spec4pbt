import SpecTecDecl0428

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$tableObject_create_entry_action:case_2:iter:5» (arg0 : evalContext) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List typedExpressionIR)) (arg3 : (_root_.List (_root_.Option typedExpressionIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option typedExpressionIR)), SpecTecCall.«$tableObject_create_entry_action:case_2:iter:5» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$tableObject_create_entry_action» (arg0 : evalContext) (arg1 : tableActionsPropertyIR) (arg2 : tableActionInterface) (arg3 : tableActionReferenceIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableActionReferenceIR, SpecTecCall.«$tableObject_create_entry_action» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$tableObject_add_entry» (arg0 : evalContext) (arg1 : tableObject) (arg2 : tableEntryPriorityInterface) (arg3 : tableKeysetInterface) (arg4 : tableActionInterface) (arg5 : (_root_.Option tableObject)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option tableObject), SpecTecCall.«$tableObject_add_entry» arg0 arg1 arg2 arg3 arg4⟩) 0 (.success (.of (arg5))) finalSupply


noncomputable def «$tableObject_add_default_action» (arg0 : evalContext) (arg1 : tableObject) (arg2 : tableActionInterface) (arg3 : tableObject) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableObject, SpecTecCall.«$tableObject_add_default_action» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$update_headerUnion» (arg0 : (_root_.List fieldValue)) (arg1 : nameIR) (arg2 : (_root_.List fieldValue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldValue), SpecTecCall.«$update_headerUnion» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$isValid_header» (arg0 : value) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$isValid_header» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$invalidate_value» (arg0 : value) (arg1 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$invalidate_value» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$invalidate_headerUnion» (arg0 : headerUnionValue) (arg1 : headerUnionValue) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨headerUnionValue, SpecTecCall.«$invalidate_headerUnion» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$invalidate_headerUnion:case_1:iter:2» (arg0 : (_root_.List value)) (arg1 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«$invalidate_headerUnion:case_1:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Call_eval:cont:iter:5» (arg0 : (_root_.List value)) (arg1 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«Call_eval:cont:iter:5» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Call_eval:cont-overflow:iter:5» (arg0 : (_root_.List value)) (arg1 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«Call_eval:cont-overflow:iter:5» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Call_eval:cont_2:iter:5» (arg0 : (_root_.List value)) (arg1 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«Call_eval:cont_2:iter:5» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Call_eval:cont-overflow_2:iter:5» (arg0 : (_root_.List value)) (arg1 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«Call_eval:cont-overflow_2:iter:5» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Call_eval:builtinIsValidMethodCallee-header-union:iter:3» (arg0 : (_root_.List value)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Call_eval:builtinIsValidMethodCallee-header-union:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$un_bnot» (arg0 : value) (arg1 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$un_bnot» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$un_plus» (arg0 : value) (arg1 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$un_plus» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$un_minus» (arg0 : value) (arg1 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$un_minus» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$un_op» (arg0 : unop) (arg1 : value) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$un_op» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_plus» (arg0 : value) (arg1 : value) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$bin_plus» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_satplus» (arg0 : value) (arg1 : value) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$bin_satplus» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_minus» (arg0 : value) (arg1 : value) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$bin_minus» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_satminus» (arg0 : value) (arg1 : value) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$bin_satminus» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_mul» (arg0 : value) (arg1 : value) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$bin_mul» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_div» (arg0 : value) (arg1 : value) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$bin_div» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_mod» (arg0 : value) (arg1 : value) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$bin_mod» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_shl» (arg0 : value) (arg1 : value) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$bin_shl» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_shr» (arg0 : value) (arg1 : value) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$bin_shr» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_le» (arg0 : value) (arg1 : value) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$bin_le» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_ge» (arg0 : value) (arg1 : value) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$bin_ge» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_lt» (arg0 : value) (arg1 : value) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$bin_lt» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_gt» (arg0 : value) (arg1 : value) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$bin_gt» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$bin_band» (arg0 : value) (arg1 : value) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$bin_band» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

end SpecTec
