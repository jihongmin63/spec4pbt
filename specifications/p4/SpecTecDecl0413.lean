import SpecTecDecl0412

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$set_priorities_of_tableEntryListIR» (arg0 : tableContext) (arg1 : (_root_.List tableEntryState)) (arg2 : tableEntryListIR) (arg3 : tableEntryListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableEntryListIR, SpecTecCall.«$set_priorities_of_tableEntryListIR» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$get_tableEntryPriority» (arg0 : (_root_.Option tableEntryPriorityIR)) (arg1 : (_root_.Option _root_.Nat)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option _root_.Nat), SpecTecCall.«$get_tableEntryPriority» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_keysetExpressionIR» (arg0 : keysetExpressionIR) (arg1 : simpleKeysetExpressionListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨simpleKeysetExpressionListIR, SpecTecCall.«$flatten_keysetExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$find_local_return_type_t» (arg0 : typingContext) (arg1 : (_root_.Option typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option typeIR), SpecTecCall.«$find_local_return_type_t» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$callable_definedFunction» (arg0 : cursor) (arg1 : typingContext) (arg2 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$callable_definedFunction» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$lvalue_as_expression» (arg0 : lvalue) (arg1 : expression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨expression, SpecTecCall.«$lvalue_as_expression» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$typedLvalueIR_as_typedExpressionIR» (arg0 : typedLvalueIR) (arg1 : (_root_.Option typedExpressionIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option typedExpressionIR), SpecTecCall.«$typedLvalueIR_as_typedExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$expression_as_lvalue» (arg0 : expression) (arg1 : (_root_.Option lvalue)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option lvalue), SpecTecCall.«$expression_as_lvalue» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$expression_as_expressionNonBrace» (arg0 : expression) (arg1 : expressionNonBrace) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨expressionNonBrace, SpecTecCall.«$expression_as_expressionNonBrace» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$typedExpressionIR_as_typedLvalueIR» (arg0 : typedExpressionIR) (arg1 : (_root_.Option typedLvalueIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option typedLvalueIR), SpecTecCall.«$typedExpressionIR_as_typedLvalueIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$subexpressions_of_typedExpressionIR» (arg0 : typedExpressionIR) (arg1 : typedExpressionListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionListIR, SpecTecCall.«$subexpressions_of_typedExpressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$subexpressions_of_typedExpressionListIR» (arg0 : typedExpressionListIR) (arg1 : typedExpressionListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionListIR, SpecTecCall.«$subexpressions_of_typedExpressionListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$subexpressions_of_typedExpressionListIR:case_1:iter:0» (arg0 : (_root_.List typedExpressionIR)) (arg1 : (_root_.List (_root_.List typedExpressionIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typedExpressionIR)), SpecTecCall.«$subexpressions_of_typedExpressionListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$subexpressions_of_expressionIR» (arg0 : expressionIR) (arg1 : typedExpressionListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionListIR, SpecTecCall.«$subexpressions_of_expressionIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$subexpressions_of_argumentIR» (arg0 : argumentIR) (arg1 : typedExpressionListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionListIR, SpecTecCall.«$subexpressions_of_argumentIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$subexpressions_of_argumentListIR» (arg0 : argumentListIR) (arg1 : typedExpressionListIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typedExpressionListIR, SpecTecCall.«$subexpressions_of_argumentListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$subexpressions_of_argumentListIR:case_1:iter:0» (arg0 : (_root_.List argumentIR)) (arg1 : (_root_.List (_root_.List typedExpressionIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List typedExpressionIR)), SpecTecCall.«$subexpressions_of_argumentListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$expressionNonBrace_as_expression» (arg0 : expressionNonBrace) (arg1 : expression) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨expression, SpecTecCall.«$expressionNonBrace_as_expression» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$parameterListIR_of_methodDef» (arg0 : methodDef) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_methodDef» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$parameterListIR_of_callableDef» (arg0 : callableDef) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_callableDef» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$find_callableDef_overloaded_e» (arg0 : cursor) (arg1 : evalContext) (arg2 : prefixedNameIR) (arg3 : (_root_.List argumentIR)) (arg4 : (_root_.Option (callResolution (cursor × callableDef)))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option (callResolution (cursor × callableDef))), SpecTecCall.«$find_callableDef_overloaded_e» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$parameterListIR_of_methodTypeDefIR» (arg0 : methodTypeDefIR) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_methodTypeDefIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$parameterListIR_of_callableTypeDefIR» (arg0 : callableTypeDefIR) (arg1 : (_root_.List parameterIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_callableTypeDefIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$find_callableDef_overloaded_t» (arg0 : cursor) (arg1 : typingContext) (arg2 : prefixedNameIR) (arg3 : (_root_.List argumentIR)) (arg4 : (_root_.Option (callResolution callableTypeDefIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option (callResolution callableTypeDefIR)), SpecTecCall.«$find_callableDef_overloaded_t» arg0 arg1 arg2 arg3⟩) 0 (.success (.of (arg4))) finalSupply


noncomputable def «$flatten_nameList» (arg0 : nameList) (arg1 : (_root_.List name)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List name), SpecTecCall.«$flatten_nameList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_namedExpressionList» (arg0 : namedExpressionList) (arg1 : (_root_.List namedExpression)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List namedExpression), SpecTecCall.«$flatten_namedExpressionList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$find_objectState_e» (arg0 : arch) (arg1 : objectId) (arg2 : (_root_.Option objectState)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option objectState), SpecTecCall.«$find_objectState_e» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$update_objectState_e» (arg0 : arch) (arg1 : objectId) (arg2 : objectState) (arg3 : (_root_.Option arch)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option arch), SpecTecCall.«$update_objectState_e» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «$V1Model_setup_hdr_argument» (arg0 : arch) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$V1Model_setup_hdr_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$V1Model_setup_meta_argument» (arg0 : arch) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$V1Model_setup_meta_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$eBPF_setup_headers_argument» (arg0 : arch) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$eBPF_setup_headers_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$PSA_setup_normal_meta_argument» (arg0 : arch) (arg1 : argumentIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨argumentIR, SpecTecCall.«$PSA_setup_normal_meta_argument» arg0⟩) 0 (.success (.of (arg1))) finalSupply

end SpecTec
