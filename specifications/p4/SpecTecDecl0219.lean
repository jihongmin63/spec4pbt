import SpecTecDecl0218

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Decl_inst:packageTypeDeclarationIR:iter:1_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:packageTypeDeclarationIR:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_inst:packageTypeDeclarationIR:iter:1:clause:1»  input0)]


noncomputable def «Constructor_call:externConstructorDef:iter:2:clause:0» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Constructor_call:externConstructorDef:iter:2:clause:1» (input0 : (_root_.List SpecTec.typeArgumentIR)) (input1 : (_root_.List SpecTec.typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeParameterIR : SpecTec.typeParameterIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.typeParameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Constructor_call:externConstructorDef:iter:2» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» typeParameterIR typeArgumentIR) : (pair typeId typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Constructor_call:externConstructorDef:iter:2_clauses» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Constructor_call:externConstructorDef:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Constructor_call:externConstructorDef:iter:2:clause:1»  input0 input1)]


noncomputable def «Constructor_call:externConstructorDef:iter:5:clause:0» (input0 : (_root_.List constructorParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List parameterInitializerOptIR)), (([] : (_root_.List typeIR)), ([] : (_root_.List id)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))))) | _ :: _ => .unmatch)


noncomputable def «Constructor_call:externConstructorDef:iter:5:clause:1» (input0 : (_root_.List constructorParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let constructorParameterIR_aligned : constructorParameterIR := «exec:2»; (let «tail:0» : (_root_.List constructorParameterIR) := «exec:1»; (match constructorParameterIR_aligned with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let _typeIR : typeIR := «exec:5»; (let id_aligned : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))), SpecTecCall.«Constructor_call:externConstructorDef:iter:5» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List parameterInitializerOptIR) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List typeIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List id) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_parameterInitializerOptIR :: «tail:3»), ((_typeIR :: «tail:4»), (id_aligned :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «Constructor_call:externConstructorDef:iter:5_clauses» (input0 : (_root_.List constructorParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Constructor_call:externConstructorDef:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Constructor_call:externConstructorDef:iter:5:clause:1»  input0)]


noncomputable def «Constructor_call:externConstructorDef:pattern-iter:6:clause:0» (input0 : (_root_.List (pair callTargetId callableDef))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List callableId)), ([] : (_root_.List callableDef))) : ((_root_.List callableId) × (_root_.List callableDef))))) | _ :: _ => .unmatch)


noncomputable def «Constructor_call:externConstructorDef:pattern-iter:6:clause:1» (input0 : (_root_.List (pair callTargetId SpecTec.callableDef))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let callableId : SpecTec.callableId := «exec:3»; (let callableDef : SpecTec.callableDef := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId SpecTec.callableDef)) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.callableId) × (_root_.List SpecTec.callableDef)), SpecTecCall.«Constructor_call:externConstructorDef:pattern-iter:6» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.callableId) × (_root_.List SpecTec.callableDef))) => (let «pattern-tail:1» : (_root_.List SpecTec.callableId) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.callableDef) := («exec:5»).2; (.pure ((((callableId :: «pattern-tail:1»), (callableDef :: «pattern-tail:2»)) : ((_root_.List SpecTec.callableId) × (_root_.List SpecTec.callableDef))))))))))))) | [] => .unmatch)


noncomputable def «Constructor_call:externConstructorDef:pattern-iter:6_clauses» (input0 : (_root_.List (pair callTargetId callableDef))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Constructor_call:externConstructorDef:pattern-iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («Constructor_call:externConstructorDef:pattern-iter:6:clause:1»  input0)]


noncomputable def «Constructor_call:externConstructorDef:iter:9:clause:0» (input0 : (_root_.List callableDef)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List externMethodDef)) : (_root_.List externMethodDef)))) | _ :: _ => .unmatch)


noncomputable def «Constructor_call:externConstructorDef:iter:9:clause:1» (input0 : (_root_.List SpecTec.callableDef)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let callableDef : SpecTec.callableDef := «exec:2»; (let «tail:0» : (_root_.List SpecTec.callableDef) := «exec:1»; (match («Constructor_call:externConstructorDef:downcast:10» callableDef) with | some «exec:3» => (let «eval:10» : SpecTec.externMethodDef := «exec:3»; (let externMethodDef : SpecTec.externMethodDef := «eval:10»; (.bind (.call ⟨(_root_.List SpecTec.externMethodDef), SpecTecCall.«Constructor_call:externConstructorDef:iter:9» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.externMethodDef)) => (let «tail:1» : (_root_.List SpecTec.externMethodDef) := «exec:4»; (.pure (((externMethodDef :: «tail:1») : (_root_.List SpecTec.externMethodDef))))))))) | none => .unmatch))) | [] => .unmatch)


noncomputable def «Constructor_call:externConstructorDef:iter:9_clauses» (input0 : (_root_.List callableDef)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Constructor_call:externConstructorDef:iter:9:clause:0»  input0), fun (_ : _root_.Unit) => («Constructor_call:externConstructorDef:iter:9:clause:1»  input0)]


noncomputable def «Constructor_call:externConstructorDef:iter:11:clause:0» (input0 : (_root_.List constructorParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List parameterInitializerOptIR)), (([] : (_root_.List typeIR)), ([] : (_root_.List id)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))))) | _ :: _ => .unmatch)


noncomputable def «Constructor_call:externConstructorDef:iter:11:clause:1» (input0 : (_root_.List constructorParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let constructorParameterIR_default : constructorParameterIR := «exec:2»; (let «tail:0» : (_root_.List constructorParameterIR) := «exec:1»; (match constructorParameterIR_default with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList' : annotationList := «exec:3»; (let _direction' : direction := «exec:4»; (let _typeIR' : typeIR := «exec:5»; (let id : SpecTec.id := «exec:6»; (let _parameterInitializerOptIR' : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List SpecTec.id))))), SpecTecCall.«Constructor_call:externConstructorDef:iter:11» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List SpecTec.id)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List parameterInitializerOptIR) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List typeIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List SpecTec.id) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList' :: «tail:1»), ((_direction' :: «tail:2»), ((_parameterInitializerOptIR' :: «tail:3»), ((_typeIR' :: «tail:4»), (id :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List SpecTec.id))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «Constructor_call:externConstructorDef:iter:11_clauses» (input0 : (_root_.List constructorParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Constructor_call:externConstructorDef:iter:11:clause:0»  input0), fun (_ : _root_.Unit) => («Constructor_call:externConstructorDef:iter:11:clause:1»  input0)]


noncomputable def «Constructor_call:externConstructorDef:iter:12:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Constructor_call:externConstructorDef:iter:12:clause:1» (input0 : (_root_.List SpecTec.id)) (input1 : (_root_.List SpecTec.id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id_default : SpecTec.id := «exec:2»; (let «tail:0» : (_root_.List SpecTec.id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let id : SpecTec.id := «exec:4»; (let «tail:1» : (_root_.List SpecTec.id) := «exec:3»; (.bind (.guard (id_default = id)) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Constructor_call:externConstructorDef:iter:12» «tail:0» «tail:1»⟩) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Constructor_call:externConstructorDef:iter:12_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List id)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Constructor_call:externConstructorDef:iter:12:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Constructor_call:externConstructorDef:iter:12:clause:1»  input0 input1)]


noncomputable def «Constructor_call:externConstructorDef:iter:13:clause:0» (input0 : instContext) (input1 : (_root_.List id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let IC_callee_4 : instContext := input0; (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.Option value))) : (_root_.List (_root_.Option value))))) | _ :: _ => .unmatch))


noncomputable def «Constructor_call:externConstructorDef:iter:13:clause:1» (input0 : instContext) (input1 : (_root_.List id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let IC_callee_4 : instContext := input0; (match input1 with | «exec:2» :: «exec:1» => (let id_cparam : id := «exec:2»; (let «tail:0» : (_root_.List id) := «exec:1»; (.bind (.call ⟨(_root_.Option value), SpecTecCall.«$find_map» id value (blockInstLayer.FRAME (instContext.BLOCK IC_callee_4)) id_cparam⟩) (fun («exec:3» : (_root_.Option value)) => (let «eval:14» : (_root_.Option value) := «exec:3»; (let value? : (_root_.Option value) := «eval:14»; (.bind (.call ⟨(_root_.List (_root_.Option value)), SpecTecCall.«Constructor_call:externConstructorDef:iter:13» IC_callee_4 «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.Option value))) => (let «tail:1» : (_root_.List (_root_.Option value)) := «exec:4»; (.pure (((value? :: «tail:1») : (_root_.List (_root_.Option value)))))))))))))) | [] => .unmatch))


noncomputable def «Constructor_call:externConstructorDef:iter:13_clauses» (input0 : instContext) (input1 : (_root_.List id)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Constructor_call:externConstructorDef:iter:13:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Constructor_call:externConstructorDef:iter:13:clause:1»  input0 input1)]


noncomputable def «Constructor_call:externConstructorDef:iter:15:clause:0» (input0 : (_root_.List (_root_.Option value))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Constructor_call:externConstructorDef:iter:15:clause:1» (input0 : (_root_.List (_root_.Option value))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let value? : (_root_.Option value) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option value)) := «exec:1»; (.bind (.guard (((_root_.Option.isSome value?) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Constructor_call:externConstructorDef:iter:15» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Constructor_call:externConstructorDef:iter:15_clauses» (input0 : (_root_.List (_root_.Option value))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Constructor_call:externConstructorDef:iter:15:clause:0»  input0), fun (_ : _root_.Unit) => («Constructor_call:externConstructorDef:iter:15:clause:1»  input0)]


noncomputable def «Constructor_call:externConstructorDef:iter:16:clause:0» (input0 : (_root_.List (_root_.Option value))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch)


noncomputable def «Constructor_call:externConstructorDef:iter:16:clause:1» (input0 : (_root_.List (_root_.Option value))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let value? : (_root_.Option value) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option value)) := «exec:1»; (match value? with | some «exec:3» => (let value_cparam : value := «exec:3»; (.bind (.call ⟨(_root_.List value), SpecTecCall.«Constructor_call:externConstructorDef:iter:16» «tail:0»⟩) (fun («exec:4» : (_root_.List value)) => (let «tail:1» : (_root_.List value) := «exec:4»; (.pure (((value_cparam :: «tail:1») : (_root_.List value)))))))) | none => .unmatch))) | [] => .unmatch)


noncomputable def «Constructor_call:externConstructorDef:iter:16_clauses» (input0 : (_root_.List (_root_.Option value))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Constructor_call:externConstructorDef:iter:16:clause:0»  input0), fun (_ : _root_.Unit) => («Constructor_call:externConstructorDef:iter:16:clause:1»  input0)]


noncomputable def «Constructor_call:externConstructorDef:iter:18:clause:0» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodDef)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId externMethodDef))) : (_root_.List (pair callTargetId externMethodDef))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Constructor_call:externConstructorDef:iter:18:clause:1» (input0 : (_root_.List SpecTec.callableId)) (input1 : (_root_.List SpecTec.externMethodDef)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let callableId : SpecTec.callableId := «exec:2»; (let «tail:0» : (_root_.List SpecTec.callableId) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let externMethodDef : SpecTec.externMethodDef := «exec:4»; (let «tail:1» : (_root_.List SpecTec.externMethodDef) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId SpecTec.externMethodDef)), SpecTecCall.«Constructor_call:externConstructorDef:iter:18» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId SpecTec.externMethodDef))) => (let «tail:2» : (_root_.List (pair callTargetId SpecTec.externMethodDef)) := «exec:5»; (.pure (((((pair.«% ':' %» callableId externMethodDef) : (pair SpecTec.callableId SpecTec.externMethodDef)) :: «tail:2») : (_root_.List (pair callTargetId SpecTec.externMethodDef)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Constructor_call:externConstructorDef:iter:18_clauses» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodDef)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Constructor_call:externConstructorDef:iter:18:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Constructor_call:externConstructorDef:iter:18:clause:1»  input0 input1)]


noncomputable def «Constructor_call:parserConstructorDef:iter:2:clause:0» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)

end SpecTec
