import SpecTecDecl0419

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def ConstructorTypeDef_wf (arg0 : bound) (arg1 : constructorTypeDefIR) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨_root_.Unit, SpecTecCall.ConstructorTypeDef_wf arg0 arg1⟩) 0 (.success (.of ((_root_.Unit.unit)))) finalSupply

namespace Notation.ConstructorTypeDef_wf
scoped notation:50 x0:51 " |- " x1:51 => _root_.SpecTec.ConstructorTypeDef_wf x0 x1
end Notation.ConstructorTypeDef_wf


noncomputable def Cast_impl (arg0 : typeIR) (arg1 : typeIR) (arg2 : castResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨castResult, SpecTecCall.Cast_impl arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

namespace Notation.Cast_impl
scoped notation:50 x0:51 " -> " x1:51 " : " x2:51 => _root_.SpecTec.Cast_impl x0 x1 x2
end Notation.Cast_impl


noncomputable def Cast_impl_neq (arg0 : typeIR) (arg1 : typeIR) (arg2 : castResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨castResult, SpecTecCall.Cast_impl_neq arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

namespace Notation.Cast_impl_neq
scoped notation:50 x0:51 " -> " x1:51 " : " x2:51 => _root_.SpecTec.Cast_impl_neq x0 x1 x2
end Notation.Cast_impl_neq


noncomputable def «Cast_impl_neq:listTypeIR:iter:2» (arg0 : typeIR) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_impl_neq:listTypeIR:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_impl_neq:tupleTypeIR:iter:2» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_impl_neq:tupleTypeIR:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_impl_neq:arrayTypeIR:iter:2» (arg0 : typeIR) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_impl_neq:arrayTypeIR:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_impl_neq:headerStackTypeIR:iter:2» (arg0 : typeIR) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_impl_neq:headerStackTypeIR:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_impl_neq:structTypeIR:iter:4» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_impl_neq:structTypeIR:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_impl_neq:headerTypeIR_2:iter:4» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_impl_neq:headerTypeIR_2:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_impl_neq:sequenceTypeIR:iter:2» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_impl_neq:sequenceTypeIR:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_impl_neq:tupleTypeIR_2:iter:3» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_impl_neq:tupleTypeIR_2:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_impl_neq:arrayTypeIR_2:iter:2» (arg0 : typeIR) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_impl_neq:arrayTypeIR_2:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_impl_neq:headerStackTypeIR_2:iter:2» (arg0 : typeIR) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_impl_neq:headerStackTypeIR_2:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_impl_neq:structTypeIR_2:iter:5» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_impl_neq:structTypeIR_2:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_impl_neq:headerTypeIR_3:iter:5» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_impl_neq:headerTypeIR_3:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_impl_neq:structTypeIR_3:iter:20» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_impl_neq:structTypeIR_3:iter:20» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_impl_neq:headerTypeIR_4:iter:20» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_impl_neq:headerTypeIR_4:iter:20» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_impl_neq:structTypeIR_4:iter:20» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_impl_neq:structTypeIR_4:iter:20» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_impl_neq:headerTypeIR_5:iter:20» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_impl_neq:headerTypeIR_5:iter:20» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def Cast_expl (arg0 : typeIR) (arg1 : typeIR) (arg2 : castResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨castResult, SpecTecCall.Cast_expl arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

namespace Notation.Cast_expl
scoped notation:50 x0:51 " -> " x1:51 " : " x2:51 => _root_.SpecTec.Cast_expl x0 x1 x2
end Notation.Cast_expl


noncomputable def Cast_expl_neq (arg0 : typeIR) (arg1 : typeIR) (arg2 : castResult) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨castResult, SpecTecCall.Cast_expl_neq arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

namespace Notation.Cast_expl_neq
scoped notation:50 x0:51 " -> " x1:51 " : " x2:51 => _root_.SpecTec.Cast_expl_neq x0 x1 x2
end Notation.Cast_expl_neq


noncomputable def «Cast_expl_neq:listTypeIR:iter:2» (arg0 : typeIR) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_expl_neq:listTypeIR:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_expl_neq:tupleTypeIR:iter:2» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_expl_neq:tupleTypeIR:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_expl_neq:arrayTypeIR:iter:2» (arg0 : typeIR) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_expl_neq:arrayTypeIR:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_expl_neq:headerStackTypeIR:iter:2» (arg0 : typeIR) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_expl_neq:headerStackTypeIR:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR:iter:4» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_expl_neq:structTypeIR:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_2:iter:4» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_expl_neq:headerTypeIR_2:iter:4» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_expl_neq:tupleTypeIR_2:iter:3» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_expl_neq:tupleTypeIR_2:iter:3» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_expl_neq:arrayTypeIR_2:iter:2» (arg0 : typeIR) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_expl_neq:arrayTypeIR_2:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_expl_neq:headerStackTypeIR_2:iter:2» (arg0 : typeIR) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_expl_neq:headerStackTypeIR_2:iter:2» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_expl_neq:structTypeIR_2:iter:5» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_expl_neq:structTypeIR_2:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply


noncomputable def «Cast_expl_neq:headerTypeIR_3:iter:5» (arg0 : (_root_.List typeIR)) (arg1 : (_root_.List typeIR)) (arg2 : (_root_.List castResult)) : Prop :=
  ∃ finalSupply : Nat, SpecTecExecution.Eval specTecProgram (.call ⟨(_root_.List castResult), SpecTecCall.«Cast_expl_neq:headerTypeIR_3:iter:5» arg0 arg1⟩) 0 (.success (.of (arg2))) finalSupply

end SpecTec
