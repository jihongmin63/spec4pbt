import SpecTecDecl0394

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «TableType_ok:rule:iter:7» (arg0 : typeId) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List _root_.String)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List _root_.String), SpecTecCall.«TableType_ok:rule:iter:7» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Decl_ok:errorDeclaration:iter:2» (arg0 : (_root_.List name)) (arg1 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List nameIR), SpecTecCall.«Decl_ok:errorDeclaration:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_ok:errorDeclaration:iter:5» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List nameIR), SpecTecCall.«Decl_ok:errorDeclaration:iter:5» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_ok:errorDeclaration:iter:6» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«Decl_ok:errorDeclaration:iter:6» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_ok:errorDeclaration:iter:7» (arg0 : (_root_.List value)) (arg1 : (_root_.List varTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List varTypeIR), SpecTecCall.«Decl_ok:errorDeclaration:iter:7» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_ok:matchKindDeclaration:iter:2» (arg0 : (_root_.List name)) (arg1 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List nameIR), SpecTecCall.«Decl_ok:matchKindDeclaration:iter:2» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_ok:matchKindDeclaration:iter:5» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«Decl_ok:matchKindDeclaration:iter:5» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_ok:matchKindDeclaration:iter:6» (arg0 : (_root_.List value)) (arg1 : (_root_.List varTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List varTypeIR), SpecTecCall.«Decl_ok:matchKindDeclaration:iter:6» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_ok:externObjectDeclaration:iter:9» (arg0 : (_root_.List callableId)) (arg1 : (_root_.List externMethodTypeDefIR)) (arg2 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List (pair callTargetId externMethodTypeDefIR)), SpecTecCall.«Decl_ok:externObjectDeclaration:iter:9» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Decl_ok:enumTypeDeclaration-non-serializable:iter:3» (arg0 : (_root_.List name)) (arg1 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List nameIR), SpecTecCall.«Decl_ok:enumTypeDeclaration-non-serializable:iter:3» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_ok:enumTypeDeclaration-non-serializable:iter:7» (arg0 : nameIR) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List id), SpecTecCall.«Decl_ok:enumTypeDeclaration-non-serializable:iter:7» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Decl_ok:enumTypeDeclaration-non-serializable:iter:8» (arg0 : nameIR) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List value), SpecTecCall.«Decl_ok:enumTypeDeclaration-non-serializable:iter:8» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Decl_ok:enumTypeDeclaration-serializable:iter:3» (arg0 : (_root_.List namedValueIR)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List value)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List nameIR) × (_root_.List value)), SpecTecCall.«Decl_ok:enumTypeDeclaration-serializable:iter:3» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply


noncomputable def «Decl_ok:enumTypeDeclaration-serializable:iter:4» (arg0 : nameIR) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List id)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List id), SpecTecCall.«Decl_ok:enumTypeDeclaration-serializable:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Decl_ok:enumTypeDeclaration-serializable:iter:5» (arg0 : (_root_.List nameIR)) (arg1 : (_root_.List value)) (arg2 : (_root_.List valueFieldIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List valueFieldIR), SpecTecCall.«Decl_ok:enumTypeDeclaration-serializable:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Decl_ok:structTypeDeclaration:pattern-iter:2» (arg0 : (_root_.List typeField)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List name)) (arg3 : (_root_.List type)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List name) × (_root_.List type))), SpecTecCall.«Decl_ok:structTypeDeclaration:pattern-iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Decl_ok:structTypeDeclaration:iter:5» (arg0 : (_root_.List (_root_.List typeId))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Decl_ok:structTypeDeclaration:iter:5» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Decl_ok:structTypeDeclaration:iter:7» (arg0 : (_root_.List name)) (arg1 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List nameIR), SpecTecCall.«Decl_ok:structTypeDeclaration:iter:7» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_ok:structTypeDeclaration:iter:9» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List fieldTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«Decl_ok:structTypeDeclaration:iter:9» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Decl_ok:structTypeDeclaration:iter:13» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List typeFieldIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeFieldIR), SpecTecCall.«Decl_ok:structTypeDeclaration:iter:13» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Decl_ok:headerTypeDeclaration:pattern-iter:2» (arg0 : (_root_.List typeField)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List name)) (arg3 : (_root_.List type)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List name) × (_root_.List type))), SpecTecCall.«Decl_ok:headerTypeDeclaration:pattern-iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Decl_ok:headerTypeDeclaration:iter:5» (arg0 : (_root_.List (_root_.List typeId))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Decl_ok:headerTypeDeclaration:iter:5» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Decl_ok:headerTypeDeclaration:iter:7» (arg0 : (_root_.List name)) (arg1 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List nameIR), SpecTecCall.«Decl_ok:headerTypeDeclaration:iter:7» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_ok:headerTypeDeclaration:iter:9» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List fieldTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«Decl_ok:headerTypeDeclaration:iter:9» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Decl_ok:headerTypeDeclaration:iter:13» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List typeFieldIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeFieldIR), SpecTecCall.«Decl_ok:headerTypeDeclaration:iter:13» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Decl_ok:headerUnionTypeDeclaration:pattern-iter:2» (arg0 : (_root_.List typeField)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List name)) (arg3 : (_root_.List type)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List name) × (_root_.List type))), SpecTecCall.«Decl_ok:headerUnionTypeDeclaration:pattern-iter:2» arg0⟩) 0 (.success (.of ((arg1, (arg2, arg3))))) finalSupply


noncomputable def «Decl_ok:headerUnionTypeDeclaration:iter:5» (arg0 : (_root_.List (_root_.List typeId))) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.«Decl_ok:headerUnionTypeDeclaration:iter:5» arg0⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply


noncomputable def «Decl_ok:headerUnionTypeDeclaration:iter:7» (arg0 : (_root_.List name)) (arg1 : (_root_.List nameIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List nameIR), SpecTecCall.«Decl_ok:headerUnionTypeDeclaration:iter:7» arg0⟩) 0 (.success (.of (arg1))) finalSupply


noncomputable def «Decl_ok:headerUnionTypeDeclaration:iter:9» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List fieldTypeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«Decl_ok:headerUnionTypeDeclaration:iter:9» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Decl_ok:headerUnionTypeDeclaration:iter:13» (arg0 : (_root_.List annotationList)) (arg1 : (_root_.List nameIR)) (arg2 : (_root_.List typeIR)) (arg3 : (_root_.List typeFieldIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List typeFieldIR), SpecTecCall.«Decl_ok:headerUnionTypeDeclaration:iter:13» arg0 arg1 arg2⟩) 0 (.success (.of (arg3))) finalSupply


noncomputable def «Decl_ok:packageTypeDeclaration:iter:3» (arg0 : (_root_.List constructorParameterIR)) (arg1 : (_root_.List annotationList)) (arg2 : (_root_.List direction)) (arg3 : (_root_.List id)) (arg4 : (_root_.List parameterInitializerOptIR)) (arg5 : (_root_.List typeIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR))))), SpecTecCall.«Decl_ok:packageTypeDeclaration:iter:3» arg0⟩) 0 (.success (.of ((arg1, (arg2, (arg3, (arg4, arg5))))))) finalSupply


noncomputable def «CallableType_ok:externMethodTypeIR:pattern-iter:3» (arg0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) (arg1 : (_root_.List callableId)) (arg2 : (_root_.List externMethodTypeDefIR)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨((_root_.List callableId) × (_root_.List externMethodTypeDefIR)), SpecTecCall.«CallableType_ok:externMethodTypeIR:pattern-iter:3» arg0⟩) 0 (.success (.of ((arg1, arg2)))) finalSupply

end SpecTec
