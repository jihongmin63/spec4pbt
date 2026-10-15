import SpecTecDecl0405

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_typeParameterListIR:case_1:iter:0» (arg0 : (_root_.List typeParameterIR)) (arg1 : (_root_.List typeParameter)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeParameter), SpecTecCall.«$lift_typeParameterListIR:case_1:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_typeParameterListIR» (arg0 : (_root_.List typeParameterIR)) (arg1 : typeParameterListOpt) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨typeParameterListOpt, SpecTecCall.«$lift_typeParameterListIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$lift_nameTypeIR» (arg0 : nameTypeIR) (arg1 : namedType) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨namedType, SpecTecCall.«$lift_nameTypeIR» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$optional_annotation_of_parameterIR''» (arg0 : annotation) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$optional_annotation_of_parameterIR''» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$optional_annotation_of_parameterIR':case_1:iter:1» (arg0 : (_root_.List annotation)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$optional_annotation_of_parameterIR':case_1:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$name_annotation_opt» (arg0 : annotation) (arg1 : (_root_.Option nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option nameIR), SpecTecCall.«$name_annotation_opt» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$name_annotation:case_1:iter:1» (arg0 : (_root_.List annotation)) (arg1 : (_root_.List (_root_.Option nameIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option nameIR)), SpecTecCall.«$name_annotation:case_1:iter:1» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$alias_to_original_lookup_map:case_1:iter:4» (arg0 : (_root_.List annotation)) (arg1 : (_root_.List (_root_.Option nameIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.Option nameIR)), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:4» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$alias_to_original_lookup_map:case_1:iter:3» (arg0 : (_root_.List (_root_.List annotation))) (arg1 : (_root_.List (_root_.List (_root_.Option nameIR)))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (_root_.List (_root_.Option nameIR))), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$assignop_as_binop» (arg0 : assignop) (arg1 : (_root_.Option binop)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.Option binop), SpecTecCall.«$assignop_as_binop» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$flatten_blockElementStatementList» (arg0 : blockElementStatementList) (arg1 : (_root_.List blockElementStatement)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List blockElementStatement), SpecTecCall.«$flatten_blockElementStatementList» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Cast_expl_neq:listTypeIR:iter:3» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:listTypeIR:iter:3» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:tupleTypeIR:iter:3» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:tupleTypeIR:iter:3» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:arrayTypeIR:iter:3» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:arrayTypeIR:iter:3» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:headerStackTypeIR:iter:3» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:headerStackTypeIR:iter:3» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR:iter:5» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:structTypeIR:iter:5» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_2:iter:5» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:headerTypeIR_2:iter:5» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:tupleTypeIR_2:iter:4» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:tupleTypeIR_2:iter:4» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:arrayTypeIR_2:iter:3» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:arrayTypeIR_2:iter:3» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:headerStackTypeIR_2:iter:3» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:headerStackTypeIR_2:iter:3» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_2:iter:6» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:structTypeIR_2:iter:6» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_3:iter:6» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:headerTypeIR_3:iter:6» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_3:iter:21» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:structTypeIR_3:iter:21» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_4:iter:21» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:headerTypeIR_4:iter:21» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_4:iter:21» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:structTypeIR_4:iter:21» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_5:iter:21» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:headerTypeIR_5:iter:21» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_impl_neq:listTypeIR:iter:3» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:listTypeIR:iter:3» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_impl_neq:tupleTypeIR:iter:3» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:tupleTypeIR:iter:3» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_impl_neq:arrayTypeIR:iter:3» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:arrayTypeIR:iter:3» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_impl_neq:headerStackTypeIR:iter:3» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:headerStackTypeIR:iter:3» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_impl_neq:structTypeIR:iter:5» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:structTypeIR:iter:5» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Cast_impl_neq:headerTypeIR_2:iter:5» (arg0 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:headerTypeIR_2:iter:5» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply

end SpecTec
