import SpecTecDecl0219

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Constructor_call:parserConstructorDef:iter:2:clause:1» (input0 : (_root_.List SpecTec.typeArgumentIR)) (input1 : (_root_.List SpecTec.typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeParameterIR : SpecTec.typeParameterIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.typeParameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Constructor_call:parserConstructorDef:iter:2» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» typeParameterIR typeArgumentIR) : (pair typeId typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Constructor_call:parserConstructorDef:iter:2_clauses» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Constructor_call:parserConstructorDef:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Constructor_call:parserConstructorDef:iter:2:clause:1»  input0 input1)]


noncomputable def «Constructor_call:parserConstructorDef:iter:5:clause:0» (input0 : (_root_.List constructorParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List parameterInitializerOptIR)), (([] : (_root_.List typeIR)), ([] : (_root_.List id)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))))) | _ :: _ => .unmatch)


noncomputable def «Constructor_call:parserConstructorDef:iter:5:clause:1» (input0 : (_root_.List constructorParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let constructorParameterIR_aligned : constructorParameterIR := «exec:2»; (let «tail:0» : (_root_.List constructorParameterIR) := «exec:1»; (match constructorParameterIR_aligned with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let _typeIR : typeIR := «exec:5»; (let id_aligned : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))), SpecTecCall.«Constructor_call:parserConstructorDef:iter:5» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List parameterInitializerOptIR) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List typeIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List id) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_parameterInitializerOptIR :: «tail:3»), ((_typeIR :: «tail:4»), (id_aligned :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «Constructor_call:parserConstructorDef:iter:5_clauses» (input0 : (_root_.List constructorParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Constructor_call:parserConstructorDef:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Constructor_call:parserConstructorDef:iter:5:clause:1»  input0)]


noncomputable def «Constructor_call:controlConstructorDef:iter:2:clause:0» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Constructor_call:controlConstructorDef:iter:2:clause:1» (input0 : (_root_.List SpecTec.typeArgumentIR)) (input1 : (_root_.List SpecTec.typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeParameterIR : SpecTec.typeParameterIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.typeParameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Constructor_call:controlConstructorDef:iter:2» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» typeParameterIR typeArgumentIR) : (pair typeId typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Constructor_call:controlConstructorDef:iter:2_clauses» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Constructor_call:controlConstructorDef:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Constructor_call:controlConstructorDef:iter:2:clause:1»  input0 input1)]


noncomputable def «Constructor_call:controlConstructorDef:iter:5:clause:0» (input0 : (_root_.List constructorParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List parameterInitializerOptIR)), (([] : (_root_.List typeIR)), ([] : (_root_.List id)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))))) | _ :: _ => .unmatch)


noncomputable def «Constructor_call:controlConstructorDef:iter:5:clause:1» (input0 : (_root_.List constructorParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let constructorParameterIR_aligned : constructorParameterIR := «exec:2»; (let «tail:0» : (_root_.List constructorParameterIR) := «exec:1»; (match constructorParameterIR_aligned with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let _typeIR : typeIR := «exec:5»; (let id_aligned : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))), SpecTecCall.«Constructor_call:controlConstructorDef:iter:5» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List parameterInitializerOptIR) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List typeIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List id) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_parameterInitializerOptIR :: «tail:3»), ((_typeIR :: «tail:4»), (id_aligned :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «Constructor_call:controlConstructorDef:iter:5_clauses» (input0 : (_root_.List constructorParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Constructor_call:controlConstructorDef:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Constructor_call:controlConstructorDef:iter:5:clause:1»  input0)]


noncomputable def «Constructor_call:controlConstructorDef:pattern-iter:6:clause:0» (input0 : (_root_.List (pair callTargetId callableDef))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List callableId)), ([] : (_root_.List callableDef))) : ((_root_.List callableId) × (_root_.List callableDef))))) | _ :: _ => .unmatch)


noncomputable def «Constructor_call:controlConstructorDef:pattern-iter:6:clause:1» (input0 : (_root_.List (pair callTargetId SpecTec.callableDef))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let callableId : SpecTec.callableId := «exec:3»; (let callableDef : SpecTec.callableDef := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId SpecTec.callableDef)) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.callableId) × (_root_.List SpecTec.callableDef)), SpecTecCall.«Constructor_call:controlConstructorDef:pattern-iter:6» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.callableId) × (_root_.List SpecTec.callableDef))) => (let «pattern-tail:1» : (_root_.List SpecTec.callableId) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.callableDef) := («exec:5»).2; (.pure ((((callableId :: «pattern-tail:1»), (callableDef :: «pattern-tail:2»)) : ((_root_.List SpecTec.callableId) × (_root_.List SpecTec.callableDef))))))))))))) | [] => .unmatch)


noncomputable def «Constructor_call:controlConstructorDef:pattern-iter:6_clauses» (input0 : (_root_.List (pair callTargetId callableDef))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Constructor_call:controlConstructorDef:pattern-iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («Constructor_call:controlConstructorDef:pattern-iter:6:clause:1»  input0)]


noncomputable def «Constructor_call:controlConstructorDef:iter:9:clause:0» (input0 : (_root_.List callableDef)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List actionDef)) : (_root_.List actionDef)))) | _ :: _ => .unmatch)


noncomputable def «Constructor_call:controlConstructorDef:iter:9:clause:1» (input0 : (_root_.List SpecTec.callableDef)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let callableDef : SpecTec.callableDef := «exec:2»; (let «tail:0» : (_root_.List SpecTec.callableDef) := «exec:1»; (match («Constructor_call:controlConstructorDef:downcast:10» callableDef) with | some «exec:3» => (let «eval:10» : SpecTec.actionDef := «exec:3»; (let actionDef : SpecTec.actionDef := «eval:10»; (.bind (.call ⟨(_root_.List SpecTec.actionDef), SpecTecCall.«Constructor_call:controlConstructorDef:iter:9» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.actionDef)) => (let «tail:1» : (_root_.List SpecTec.actionDef) := «exec:4»; (.pure (((actionDef :: «tail:1») : (_root_.List SpecTec.actionDef))))))))) | none => .unmatch))) | [] => .unmatch)


noncomputable def «Constructor_call:controlConstructorDef:iter:9_clauses» (input0 : (_root_.List callableDef)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Constructor_call:controlConstructorDef:iter:9:clause:0»  input0), fun (_ : _root_.Unit) => («Constructor_call:controlConstructorDef:iter:9:clause:1»  input0)]


noncomputable def «Constructor_call:controlConstructorDef:iter:11:clause:0» (input0 : (_root_.List actionDef)) (input1 : (_root_.List callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId actionDef))) : (_root_.List (pair callTargetId actionDef))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Constructor_call:controlConstructorDef:iter:11:clause:1» (input0 : (_root_.List SpecTec.actionDef)) (input1 : (_root_.List SpecTec.callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let actionDef : SpecTec.actionDef := «exec:2»; (let «tail:0» : (_root_.List SpecTec.actionDef) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let callableId : SpecTec.callableId := «exec:4»; (let «tail:1» : (_root_.List SpecTec.callableId) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId SpecTec.actionDef)), SpecTecCall.«Constructor_call:controlConstructorDef:iter:11» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId SpecTec.actionDef))) => (let «tail:2» : (_root_.List (pair callTargetId SpecTec.actionDef)) := «exec:5»; (.pure (((((pair.«% ':' %» callableId actionDef) : (pair SpecTec.callableId SpecTec.actionDef)) :: «tail:2») : (_root_.List (pair callTargetId SpecTec.actionDef)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Constructor_call:controlConstructorDef:iter:11_clauses» (input0 : (_root_.List actionDef)) (input1 : (_root_.List callableId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Constructor_call:controlConstructorDef:iter:11:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Constructor_call:controlConstructorDef:iter:11:clause:1»  input0 input1)]


noncomputable def «Constructor_call:controlConstructorDef:iter:13:clause:0» (input0 : (_root_.List actionDef)) (input1 : (_root_.List callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId actionDef))) : (_root_.List (pair callTargetId actionDef))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Constructor_call:controlConstructorDef:iter:13:clause:1» (input0 : (_root_.List SpecTec.actionDef)) (input1 : (_root_.List SpecTec.callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let actionDef : SpecTec.actionDef := «exec:2»; (let «tail:0» : (_root_.List SpecTec.actionDef) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let callableId : SpecTec.callableId := «exec:4»; (let «tail:1» : (_root_.List SpecTec.callableId) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId SpecTec.actionDef)), SpecTecCall.«Constructor_call:controlConstructorDef:iter:13» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId SpecTec.actionDef))) => (let «tail:2» : (_root_.List (pair callTargetId SpecTec.actionDef)) := «exec:5»; (.pure (((((pair.«% ':' %» callableId actionDef) : (pair SpecTec.callableId SpecTec.actionDef)) :: «tail:2») : (_root_.List (pair callTargetId SpecTec.actionDef)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Constructor_call:controlConstructorDef:iter:13_clauses» (input0 : (_root_.List actionDef)) (input1 : (_root_.List callableId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Constructor_call:controlConstructorDef:iter:13:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Constructor_call:controlConstructorDef:iter:13:clause:1»  input0 input1)]


noncomputable def «Constructor_call:packageConstructorDef:iter:2:clause:0» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Constructor_call:packageConstructorDef:iter:2:clause:1» (input0 : (_root_.List SpecTec.typeArgumentIR)) (input1 : (_root_.List SpecTec.typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeParameterIR : SpecTec.typeParameterIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.typeParameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Constructor_call:packageConstructorDef:iter:2» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» typeParameterIR typeArgumentIR) : (pair typeId typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Constructor_call:packageConstructorDef:iter:2_clauses» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Constructor_call:packageConstructorDef:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Constructor_call:packageConstructorDef:iter:2:clause:1»  input0 input1)]


noncomputable def «Constructor_call:packageConstructorDef:iter:5:clause:0» (input0 : (_root_.List constructorParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List parameterInitializerOptIR)), (([] : (_root_.List typeIR)), ([] : (_root_.List id)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))))) | _ :: _ => .unmatch)


noncomputable def «Constructor_call:packageConstructorDef:iter:5:clause:1» (input0 : (_root_.List constructorParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let constructorParameterIR_aligned : constructorParameterIR := «exec:2»; (let «tail:0» : (_root_.List constructorParameterIR) := «exec:1»; (match constructorParameterIR_aligned with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let _typeIR : typeIR := «exec:5»; (let id_aligned : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))), SpecTecCall.«Constructor_call:packageConstructorDef:iter:5» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List parameterInitializerOptIR) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List typeIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List id) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_parameterInitializerOptIR :: «tail:3»), ((_typeIR :: «tail:4»), (id_aligned :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «Constructor_call:packageConstructorDef:iter:5_clauses» (input0 : (_root_.List constructorParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Constructor_call:packageConstructorDef:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Constructor_call:packageConstructorDef:iter:5:clause:1»  input0)]


noncomputable def «$merge_frames:case_1:pattern-iter:0:clause:0» (input0 : (_root_.List (pair _root_.String value))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List id)), ([] : (_root_.List value))) : ((_root_.List id) × (_root_.List value))))) | _ :: _ => .unmatch)


noncomputable def «$merge_frames:case_1:pattern-iter:0:clause:1» (input0 : (_root_.List (pair _root_.String SpecTec.value))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let id : SpecTec.id := «exec:3»; (let value : SpecTec.value := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair _root_.String SpecTec.value)) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.id) × (_root_.List SpecTec.value)), SpecTecCall.«$merge_frames:case_1:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.id) × (_root_.List SpecTec.value))) => (let «pattern-tail:1» : (_root_.List SpecTec.id) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.value) := («exec:5»).2; (.pure ((((id :: «pattern-tail:1»), (value :: «pattern-tail:2»)) : ((_root_.List SpecTec.id) × (_root_.List SpecTec.value))))))))))))) | [] => .unmatch)


noncomputable def «$merge_frames:case_1:pattern-iter:0_clauses» (input0 : (_root_.List (pair _root_.String value))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$merge_frames:case_1:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$merge_frames:case_1:pattern-iter:0:clause:1»  input0)]

end SpecTec
