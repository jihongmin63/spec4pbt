import SpecTecDecl0386

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Type_wf:structTypeIR:iter:4» (arg0 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:structTypeIR:iter:4» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$nestable_header:row_8:pattern-iter:0» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$nestable_header:row_8:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$nestable_struct_in_header:row_7:pattern-iter:0» (arg0 : (_root_.List fieldTypeIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List nameIR)) (arg3 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$nestable_struct_in_header:row_7:pattern-iter:0» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «$nestable_struct_in_header» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_struct_in_header» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nestable_struct_in_header:row_7:iter:2» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$nestable_struct_in_header:row_7:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nestable_header:row_8:iter:2» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$nestable_header:row_8:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nestable_array_in_header» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_array_in_header» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nestable_header» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_header» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Type_wf:headerTypeIR:iter:4» (arg0 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:headerTypeIR:iter:4» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$nestable_headerUnion» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_headerUnion» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Type_wf:headerUnionTypeIR:iter:4» (arg0 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Type_wf:headerUnionTypeIR:iter:4» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$nestable_new_in_enum_serializable» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_new_in_enum_serializable» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nestable_enum_serializable» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_enum_serializable» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nestable_tuple_in_set» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_tuple_in_set» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nestable_tuple_in_set:row_6:iter:0» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$nestable_tuple_in_set:row_6:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nestable_set:row_7:iter:0» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$nestable_set:row_7:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nestable_sequence_in_set» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_sequence_in_set» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nestable_sequence_in_set:row_6:iter:0» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$nestable_sequence_in_set:row_6:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nestable_sequence_in_set:row_8:iter:0» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$nestable_sequence_in_set:row_8:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nestable_set:row_9:iter:0» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List _root_.Bool)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$nestable_set:row_9:iter:0» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nestable_set» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_set» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «$nestable_action» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_action» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «CallableType_wf:actionTypeIR:iter:6» (arg0 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:actionTypeIR:iter:6» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$nestable_definedFunction» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_definedFunction» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «CallableType_wf:definedFunctionTypeIR:iter:5» (arg0 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:definedFunctionTypeIR:iter:5» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$nestable_externFunction» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_externFunction» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «CallableType_wf:externFunctionTypeIR:iter:3» (arg0 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:externFunctionTypeIR:iter:3» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$nestable_externMethod» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_externMethod» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «CallableType_wf:non-abstract:iter:3» (arg0 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:non-abstract:iter:3» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «CallableType_wf:abstract:iter:5» (arg0 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:abstract:iter:5» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «$nestable_parserApplyMethod» (arg0 : typeIR) (arg1 : _root_.Bool) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Bool, SpecTecCall.«$nestable_parserApplyMethod» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «CallableType_wf:parserApplyMethodTypeIR:iter:5» (arg0 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:parserApplyMethodTypeIR:iter:5» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply

end SpecTec
