import SpecTecDecl0286

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «CallableType_wf:definedFunctionTypeIR:iter:1:clause:0» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))


noncomputable def «CallableType_wf:definedFunctionTypeIR:iter:1:clause:1» (input0 : bound) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨_root_.Unit, SpecTecCall.ParameterType_wf B parameterIR⟩) (fun («exec:3» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:definedFunctionTypeIR:iter:1» B «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))


noncomputable def «CallableType_wf:definedFunctionTypeIR:iter:1_clauses» (input0 : bound) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableType_wf:definedFunctionTypeIR:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («CallableType_wf:definedFunctionTypeIR:iter:1:clause:1»  input0 input1)]


noncomputable def «CallableType_wf:externFunctionTypeIR:iter:1:clause:0» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))


noncomputable def «CallableType_wf:externFunctionTypeIR:iter:1:clause:1» (input0 : bound) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨_root_.Unit, SpecTecCall.ParameterType_wf B parameterIR⟩) (fun («exec:3» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:externFunctionTypeIR:iter:1» B «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))


noncomputable def «CallableType_wf:externFunctionTypeIR:iter:1_clauses» (input0 : bound) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableType_wf:externFunctionTypeIR:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («CallableType_wf:externFunctionTypeIR:iter:1:clause:1»  input0 input1)]


noncomputable def «CallableType_wf:non-abstract:iter:1:clause:0» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))


noncomputable def «CallableType_wf:non-abstract:iter:1:clause:1» (input0 : bound) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨_root_.Unit, SpecTecCall.ParameterType_wf B parameterIR⟩) (fun («exec:3» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:non-abstract:iter:1» B «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))


noncomputable def «CallableType_wf:non-abstract:iter:1_clauses» (input0 : bound) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableType_wf:non-abstract:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («CallableType_wf:non-abstract:iter:1:clause:1»  input0 input1)]


noncomputable def «CallableType_wf:abstract:iter:1:clause:0» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))


noncomputable def «CallableType_wf:abstract:iter:1:clause:1» (input0 : bound) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨_root_.Unit, SpecTecCall.ParameterType_wf B parameterIR⟩) (fun («exec:3» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:abstract:iter:1» B «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))


noncomputable def «CallableType_wf:abstract:iter:1_clauses» (input0 : bound) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableType_wf:abstract:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («CallableType_wf:abstract:iter:1:clause:1»  input0 input1)]


noncomputable def «CallableType_wf:parserApplyMethodTypeIR:iter:1:clause:0» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))


noncomputable def «CallableType_wf:parserApplyMethodTypeIR:iter:1:clause:1» (input0 : bound) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨_root_.Unit, SpecTecCall.ParameterType_wf B parameterIR⟩) (fun («exec:3» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:parserApplyMethodTypeIR:iter:1» B «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))


noncomputable def «CallableType_wf:parserApplyMethodTypeIR:iter:1_clauses» (input0 : bound) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableType_wf:parserApplyMethodTypeIR:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («CallableType_wf:parserApplyMethodTypeIR:iter:1:clause:1»  input0 input1)]


noncomputable def «CallableType_wf:controlApplyMethodTypeIR:iter:1:clause:0» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))


noncomputable def «CallableType_wf:controlApplyMethodTypeIR:iter:1:clause:1» (input0 : bound) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨_root_.Unit, SpecTecCall.ParameterType_wf B parameterIR⟩) (fun («exec:3» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«CallableType_wf:controlApplyMethodTypeIR:iter:1» B «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))


noncomputable def «CallableType_wf:controlApplyMethodTypeIR:iter:1_clauses» (input0 : bound) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableType_wf:controlApplyMethodTypeIR:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («CallableType_wf:controlApplyMethodTypeIR:iter:1:clause:1»  input0 input1)]


noncomputable def «CallableTypeDef_wf:clause:0» (input0 : bound) (input1 : SpecTec.callableTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (let callableTypeDefIR : SpecTec.callableTypeDefIR := input1; (.bind (.call ⟨((_root_.List typeParameterIR) × (_root_.List typeParameterIR)), SpecTecCall.«$typeParameterListIR_of_callableTypeDefIR» callableTypeDefIR⟩) (fun («exec:1» : ((_root_.List typeParameterIR) × (_root_.List typeParameterIR))) => (let «eval:0» : ((_root_.List typeParameterIR) × (_root_.List typeParameterIR)) := «exec:1»; (let «typeParameterIR_expl*» : (_root_.List typeParameterIR) := («eval:0»).1; (let «typeParameterIR_impl*» : (_root_.List typeParameterIR) := («eval:0»).2; (let «typeParameterIR*» : (_root_.List typeParameterIR) := («typeParameterIR_expl*» ++ «typeParameterIR_impl*»); (.bind (.call ⟨_root_.Bool, SpecTecCall.«$distinct_» typeId «typeParameterIR*»⟩) (fun («exec:2» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:2»; (.bind (.guard ((«eval:1» = true))) (fun (_ : Unit) => (.bind (.call ⟨callableTypeIR, SpecTecCall.«$callableTypeIR_of_callableTypeDefIR» callableTypeDefIR⟩) (fun («exec:3» : callableTypeIR) => (let «eval:2» : callableTypeIR := «exec:3»; (let callableTypeIR_base : callableTypeIR := «eval:2»; (let B_inner : bound := («$union_set» B ((set.«`{ % `}» «typeParameterIR*») : (set typeId))); (.bind (.call ⟨_root_.Unit, SpecTecCall.CallableType_wf B_inner callableTypeIR_base⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))))))))))))))


noncomputable def CallableTypeDef_wf_clauses (input0 : bound) (input1 : callableTypeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableTypeDef_wf:clause:0»  input0 input1)]


noncomputable def «TypeDef_wf:clause:0» (input0 : bound) (input1 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (let typeDefIR : SpecTec.typeDefIR := input1; (.bind (.call ⟨((_root_.List typeParameterIR) × (_root_.List typeParameterIR)), SpecTecCall.«$typeParameterListIR_of_typeDefIR» typeDefIR⟩) (fun («exec:1» : ((_root_.List typeParameterIR) × (_root_.List typeParameterIR))) => (let «eval:0» : ((_root_.List typeParameterIR) × (_root_.List typeParameterIR)) := «exec:1»; (let «typeParameterIR_expl*» : (_root_.List typeParameterIR) := («eval:0»).1; (let «typeParameterIR_impl*» : (_root_.List typeParameterIR) := («eval:0»).2; (let «typeParameterIR*» : (_root_.List typeParameterIR) := («typeParameterIR_expl*» ++ «typeParameterIR_impl*»); (.bind (.call ⟨_root_.Bool, SpecTecCall.«$distinct_» typeId «typeParameterIR*»⟩) (fun («exec:2» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:2»; (.bind (.guard ((«eval:1» = true))) (fun (_ : Unit) => (.bind (.call ⟨typeIR, SpecTecCall.«$typeIR_of_typeDefIR» typeDefIR⟩) (fun («exec:3» : typeIR) => (let «eval:2» : typeIR := «exec:3»; (let typeIR_base : typeIR := «eval:2»; (let B_inner : bound := («$union_set» B ((set.«`{ % `}» «typeParameterIR*») : (set typeId))); (.bind (.call ⟨_root_.Unit, SpecTecCall.Type_wf B_inner typeIR_base⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))))))))))))))


noncomputable def TypeDef_wf_clauses (input0 : bound) (input1 : typeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («TypeDef_wf:clause:0»  input0 input1)]


noncomputable def «ConstructorParameterType_wf:clause:0» (input0 : bound) (input1 : parameterIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (let constructorParameterIR : SpecTec.constructorParameterIR := input1; (match constructorParameterIR with | .«% % % % %» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:1»; (let direction : SpecTec.direction := «exec:2»; (let _typeIR : typeIR := «exec:3»; (let _id : id := «exec:4»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:5»; (.bind (.guard (((«exec:match:direction:_EMPTY» direction) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.ParameterType_wf B constructorParameterIR⟩) (fun («exec:6» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))))))


noncomputable def ConstructorParameterType_wf_clauses (input0 : bound) (input1 : parameterIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («ConstructorParameterType_wf:clause:0»  input0 input1)]


noncomputable def «ConstructorType_wf:externObjectTypeIR:iter:0:clause:0» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))


noncomputable def «ConstructorType_wf:externObjectTypeIR:iter:0:clause:1» (input0 : bound) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨_root_.Unit, SpecTecCall.ConstructorParameterType_wf B parameterIR⟩) (fun («exec:3» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«ConstructorType_wf:externObjectTypeIR:iter:0» B «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))


noncomputable def «ConstructorType_wf:externObjectTypeIR:iter:0_clauses» (input0 : bound) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («ConstructorType_wf:externObjectTypeIR:iter:0:clause:0»  input0 input1), fun (_ : _root_.Unit) => («ConstructorType_wf:externObjectTypeIR:iter:0:clause:1»  input0 input1)]


noncomputable def «ConstructorType_wf:parserObjectTypeIR:iter:0:clause:0» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))


noncomputable def «ConstructorType_wf:parserObjectTypeIR:iter:0:clause:1» (input0 : bound) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨_root_.Unit, SpecTecCall.ConstructorParameterType_wf B parameterIR⟩) (fun («exec:3» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«ConstructorType_wf:parserObjectTypeIR:iter:0» B «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))


noncomputable def «ConstructorType_wf:parserObjectTypeIR:iter:0_clauses» (input0 : bound) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («ConstructorType_wf:parserObjectTypeIR:iter:0:clause:0»  input0 input1), fun (_ : _root_.Unit) => («ConstructorType_wf:parserObjectTypeIR:iter:0:clause:1»  input0 input1)]


noncomputable def «ConstructorType_wf:controlObjectTypeIR:iter:0:clause:0» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch))


noncomputable def «ConstructorType_wf:controlObjectTypeIR:iter:0:clause:1» (input0 : bound) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let B : bound := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨_root_.Unit, SpecTecCall.ConstructorParameterType_wf B parameterIR⟩) (fun («exec:3» : _root_.Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«ConstructorType_wf:controlObjectTypeIR:iter:0» B «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))

end SpecTec
