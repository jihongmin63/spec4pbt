import SpecTecDecl0170

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Type_wf:serializable:pattern-iter:1:clause:0» (input0 : (_root_.List valueFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List value)), ([] : (_root_.List nameIR))) : ((_root_.List value) × (_root_.List nameIR))))) | _ :: _ => .unmatch)


noncomputable def «Type_wf:serializable:pattern-iter:1:clause:1» (input0 : (_root_.List valueFieldIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% '=' % ';'» «exec:3» «exec:4» => (let nameIR_field : nameIR := «exec:3»; (let _value : value := «exec:4»; (let «pattern-tail:0» : (_root_.List valueFieldIR) := «exec:1»; (.bind (.call ⟨((_root_.List value) × (_root_.List nameIR)), SpecTecCall.«Type_wf:serializable:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List value) × (_root_.List nameIR))) => (let «pattern-tail:1» : (_root_.List value) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List nameIR) := («exec:5»).2; (.pure ((((_value :: «pattern-tail:1»), (nameIR_field :: «pattern-tail:2»)) : ((_root_.List value) × (_root_.List nameIR))))))))))))) | [] => .unmatch)


noncomputable def «Type_wf:serializable:pattern-iter:1_clauses» (input0 : (_root_.List valueFieldIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_wf:serializable:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Type_wf:serializable:pattern-iter:1:clause:1»  input0)]


noncomputable def «Type_wf:externObjectTypeIR:pattern-iter:1:clause:0» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List callableId)), ([] : (_root_.List externMethodTypeDefIR))) : ((_root_.List callableId) × (_root_.List externMethodTypeDefIR))))) | _ :: _ => .unmatch)


noncomputable def «Type_wf:externObjectTypeIR:pattern-iter:1:clause:1» (input0 : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let _callableId : callableId := «exec:3»; (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR)) := «exec:1»; (.bind (.call ⟨((_root_.List callableId) × (_root_.List SpecTec.externMethodTypeDefIR)), SpecTecCall.«Type_wf:externObjectTypeIR:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List callableId) × (_root_.List SpecTec.externMethodTypeDefIR))) => (let «pattern-tail:1» : (_root_.List callableId) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.externMethodTypeDefIR) := («exec:5»).2; (.pure ((((_callableId :: «pattern-tail:1»), (externMethodTypeDefIR :: «pattern-tail:2»)) : ((_root_.List callableId) × (_root_.List SpecTec.externMethodTypeDefIR))))))))))))) | [] => .unmatch)


noncomputable def «Type_wf:externObjectTypeIR:pattern-iter:1_clauses» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_wf:externObjectTypeIR:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Type_wf:externObjectTypeIR:pattern-iter:1:clause:1»  input0)]


noncomputable def «Type_wf:non-default_2:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Type_wf:non-default_2:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Type_wf:non-default_2:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((nameIR_field :: «pattern-tail:2»), (typeIR_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «Type_wf:non-default_2:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_wf:non-default_2:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Type_wf:non-default_2:pattern-iter:1:clause:1»  input0)]


noncomputable def «Type_wf:default_2:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «Type_wf:default_2:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«Type_wf:default_2:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((nameIR_field :: «pattern-tail:2»), (typeIR_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «Type_wf:default_2:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Type_wf:default_2:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Type_wf:default_2:pattern-iter:1:clause:1»  input0)]


noncomputable def «CallableType_wf:actionTypeIR:iter:4:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List id)), (([] : (_root_.List parameterInitializerOptIR)), (([] : (_root_.List direction)), ([] : (_root_.List typeIR)))))) : ((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR)))))))) | _ :: _ => .unmatch)


noncomputable def «CallableType_wf:actionTypeIR:iter:4:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (match parameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList' : annotationList := «exec:3»; (let direction : SpecTec.direction := «exec:4»; (let typeIR : SpecTec.typeIR := «exec:5»; (let _id : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List SpecTec.direction) × (_root_.List SpecTec.typeIR))))), SpecTecCall.«CallableType_wf:actionTypeIR:iter:4» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List SpecTec.direction) × (_root_.List SpecTec.typeIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List id) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List parameterInitializerOptIR) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List SpecTec.direction) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List SpecTec.typeIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList' :: «tail:1»), ((_id :: «tail:2»), ((_parameterInitializerOptIR :: «tail:3»), ((direction :: «tail:4»), (typeIR :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List SpecTec.direction) × (_root_.List SpecTec.typeIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «CallableType_wf:actionTypeIR:iter:4_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableType_wf:actionTypeIR:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («CallableType_wf:actionTypeIR:iter:4:clause:1»  input0)]


noncomputable def «CallableType_wf:definedFunctionTypeIR:iter:4:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List id)), (([] : (_root_.List parameterInitializerOptIR)), ([] : (_root_.List typeIR)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))))) | _ :: _ => .unmatch)


noncomputable def «CallableType_wf:definedFunctionTypeIR:iter:4:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (match parameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let typeIR : SpecTec.typeIR := «exec:5»; (let _id : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))), SpecTecCall.«CallableType_wf:definedFunctionTypeIR:iter:4» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List id) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List parameterInitializerOptIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List SpecTec.typeIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_id :: «tail:3»), ((_parameterInitializerOptIR :: «tail:4»), (typeIR :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «CallableType_wf:definedFunctionTypeIR:iter:4_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableType_wf:definedFunctionTypeIR:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («CallableType_wf:definedFunctionTypeIR:iter:4:clause:1»  input0)]


noncomputable def «CallableType_wf:externFunctionTypeIR:iter:2:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List id)), (([] : (_root_.List parameterInitializerOptIR)), ([] : (_root_.List typeIR)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))))) | _ :: _ => .unmatch)


noncomputable def «CallableType_wf:externFunctionTypeIR:iter:2:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (match parameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let typeIR : SpecTec.typeIR := «exec:5»; (let _id : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))), SpecTecCall.«CallableType_wf:externFunctionTypeIR:iter:2» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List id) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List parameterInitializerOptIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List SpecTec.typeIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_id :: «tail:3»), ((_parameterInitializerOptIR :: «tail:4»), (typeIR :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «CallableType_wf:externFunctionTypeIR:iter:2_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableType_wf:externFunctionTypeIR:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («CallableType_wf:externFunctionTypeIR:iter:2:clause:1»  input0)]


noncomputable def «CallableType_wf:non-abstract:iter:2:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List id)), (([] : (_root_.List parameterInitializerOptIR)), ([] : (_root_.List typeIR)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))))) | _ :: _ => .unmatch)


noncomputable def «CallableType_wf:non-abstract:iter:2:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (match parameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let typeIR : SpecTec.typeIR := «exec:5»; (let _id : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))), SpecTecCall.«CallableType_wf:non-abstract:iter:2» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List id) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List parameterInitializerOptIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List SpecTec.typeIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_id :: «tail:3»), ((_parameterInitializerOptIR :: «tail:4»), (typeIR :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «CallableType_wf:non-abstract:iter:2_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableType_wf:non-abstract:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («CallableType_wf:non-abstract:iter:2:clause:1»  input0)]


noncomputable def «CallableType_wf:abstract:iter:4:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List id)), (([] : (_root_.List parameterInitializerOptIR)), ([] : (_root_.List typeIR)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))))) | _ :: _ => .unmatch)


noncomputable def «CallableType_wf:abstract:iter:4:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (match parameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let typeIR : SpecTec.typeIR := «exec:5»; (let _id : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))), SpecTecCall.«CallableType_wf:abstract:iter:4» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List id) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List parameterInitializerOptIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List SpecTec.typeIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_id :: «tail:3»), ((_parameterInitializerOptIR :: «tail:4»), (typeIR :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «CallableType_wf:abstract:iter:4_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableType_wf:abstract:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («CallableType_wf:abstract:iter:4:clause:1»  input0)]


noncomputable def «CallableType_wf:parserApplyMethodTypeIR:iter:4:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List id)), (([] : (_root_.List parameterInitializerOptIR)), ([] : (_root_.List typeIR)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))))) | _ :: _ => .unmatch)


noncomputable def «CallableType_wf:parserApplyMethodTypeIR:iter:4:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (match parameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let typeIR : SpecTec.typeIR := «exec:5»; (let _id : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))), SpecTecCall.«CallableType_wf:parserApplyMethodTypeIR:iter:4» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List id) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List parameterInitializerOptIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List SpecTec.typeIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_id :: «tail:3»), ((_parameterInitializerOptIR :: «tail:4»), (typeIR :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «CallableType_wf:parserApplyMethodTypeIR:iter:4_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableType_wf:parserApplyMethodTypeIR:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («CallableType_wf:parserApplyMethodTypeIR:iter:4:clause:1»  input0)]


noncomputable def «CallableType_wf:controlApplyMethodTypeIR:iter:4:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List id)), (([] : (_root_.List parameterInitializerOptIR)), ([] : (_root_.List typeIR)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))))) | _ :: _ => .unmatch)


noncomputable def «CallableType_wf:controlApplyMethodTypeIR:iter:4:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (match parameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let typeIR : SpecTec.typeIR := «exec:5»; (let _id : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))), SpecTecCall.«CallableType_wf:controlApplyMethodTypeIR:iter:4» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List id) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List parameterInitializerOptIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List SpecTec.typeIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_id :: «tail:3»), ((_parameterInitializerOptIR :: «tail:4»), (typeIR :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))))))))))))))))))))) | [] => .unmatch)

end SpecTec
