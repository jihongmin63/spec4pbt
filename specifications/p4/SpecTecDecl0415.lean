import SpecTecDecl0414

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$init_tableEntries:case_1:iter:0» (arg0 : (_root_.List tablePropertyIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$init_tableEntries:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$init_tableEntries:case_2:iter:0» (arg0 : (_root_.List tablePropertyIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$init_tableEntries:case_2:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$init_tableEntries» (arg0 : tablePropertyListIR) (arg1 : tableEntriesPropertyIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableEntriesPropertyIR, SpecTecCall.«$init_tableEntries» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$init_tableKeys:case_1:iter:0» (arg0 : (_root_.List tablePropertyIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$init_tableKeys:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$init_tableKeys:case_2:iter:0» (arg0 : (_root_.List tablePropertyIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$init_tableKeys:case_2:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$init_tableKeys» (arg0 : tablePropertyListIR) (arg1 : tableKeysPropertyIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableKeysPropertyIR, SpecTecCall.«$init_tableKeys» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$init_table» (arg0 : tablePropertyListIR) (arg1 : tableObjectProperty) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨tableObjectProperty, SpecTecCall.«$init_table» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_typeArgumentList» (arg0 : typeArgumentList) (arg1 : (_root_.List typeArgument)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeArgument), SpecTecCall.«$flatten_typeArgumentList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$typeIR_of_typeDefIR» (arg0 : typeDefIR) (arg1 : typeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeIR, SpecTecCall.«$typeIR_of_typeDefIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$typeParameterListIR_of_typeDefIR» (arg0 : typeDefIR) (arg1 : ((_root_.List typeParameterIR) × (_root_.List typeParameterIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List typeParameterIR) × (_root_.List typeParameterIR)), SpecTecCall.«$typeParameterListIR_of_typeDefIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_monomorphic_typeDefIR» (arg0 : typeDefIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_monomorphic_typeDefIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$is_polymorphic_typeDefIR» (arg0 : typeDefIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_polymorphic_typeDefIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$typeId_of_typeDefIR» (arg0 : typeDefIR) (arg1 : typeId) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeId, SpecTecCall.«$typeId_of_typeDefIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_typeDefIR_as_typeName» (arg0 : typeDefIR) (arg1 : typeName) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeName, SpecTecCall.«$lift_typeDefIR_as_typeName» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$cast_array» (arg0 : typeIR) (arg1 : arrayValue) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$cast_array» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$is_concrete_extern_object'» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$is_concrete_extern_object'» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$cast_header_stack» (arg0 : typeIR) (arg1 : headerStackValue) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$cast_header_stack» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_header» (arg0 : typeIR) (arg1 : headerValue) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$cast_header» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_header_union» (arg0 : typeIR) (arg1 : headerUnionValue) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$cast_header_union» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_string» (arg0 : typeIR) (arg1 : stringValue) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$cast_string» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$cast_struct» (arg0 : typeIR) (arg1 : structValue) (arg2 : value) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨value, SpecTecCall.«$cast_struct» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «$unroll_typeIR» (arg0 : typeIR) (arg1 : typeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeIR, SpecTecCall.«$unroll_typeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$unroll_aliasTypeIR» (arg0 : typeIR) (arg1 : typeIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeIR, SpecTecCall.«$unroll_aliasTypeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeIR» (arg0 : typeIR) (arg1 : bound) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨bound, SpecTecCall.«$free_typeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeIR:case_6:iter:1» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_6:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeIR:case_9:iter:3» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_9:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeIR:case_9:iter:6» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_9:iter:6» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeIR:case_10:iter:3» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_10:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeIR:case_10:iter:6» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_10:iter:6» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeIR:case_11:iter:3» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_11:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeIR:case_11:iter:6» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_11:iter:6» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$free_typeIR:case_14:iter:3» (arg0 : (_root_.List typeArgumentIR)) (arg1 : (_root_.List (set _root_.String))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_14:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply

end SpecTec
