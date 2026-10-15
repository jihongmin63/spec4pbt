import SpecTecDecl0213

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$resolve_constraint:case_2:iter:7_clauses» (input0 : (_root_.List typeId)) (input1 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$resolve_constraint:case_2:iter:7:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$resolve_constraint:case_2:iter:7:clause:1»  input0 input1)]


noncomputable def «$resolve_constraint:case_2:iter:8:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$resolve_constraint:case_2:iter:8:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_t : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeId_t : typeId := «exec:4»; (let «tail:1» : (_root_.List typeId) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$resolve_constraint:case_2:iter:8» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» typeId_t typeIR_t) : (pair typeId typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$resolve_constraint:case_2:iter:8_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$resolve_constraint:case_2:iter:8:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$resolve_constraint:case_2:iter:8:clause:1»  input0 input1)]


noncomputable def «$resolve_constraint:case_3:pattern-iter:0:clause:0» (input0 : (_root_.List (pair _root_.String infer))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List infer)), ([] : (_root_.List typeId))) : ((_root_.List infer) × (_root_.List typeId))))) | _ :: _ => .unmatch)


noncomputable def «$resolve_constraint:case_3:pattern-iter:0:clause:1» (input0 : (_root_.List (pair _root_.String infer))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let typeId_t : typeId := «exec:3»; (let infer_t : infer := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair _root_.String infer)) := «exec:1»; (.bind (.call ⟨((_root_.List infer) × (_root_.List typeId)), SpecTecCall.«$resolve_constraint:case_3:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List infer) × (_root_.List typeId))) => (let «pattern-tail:1» : (_root_.List infer) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List typeId) := («exec:5»).2; (.pure ((((infer_t :: «pattern-tail:1»), (typeId_t :: «pattern-tail:2»)) : ((_root_.List infer) × (_root_.List typeId))))))))))))) | [] => .unmatch)


noncomputable def «$resolve_constraint:case_3:pattern-iter:0_clauses» (input0 : (_root_.List (pair _root_.String infer))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$resolve_constraint:case_3:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$resolve_constraint:case_3:pattern-iter:0:clause:1»  input0)]


noncomputable def «$resolve_constraint:case_3:iter:3:clause:0» (input0 : (_root_.List infer)) (input1 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String infer))) : (_root_.List (pair _root_.String infer))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$resolve_constraint:case_3:iter:3:clause:1» (input0 : (_root_.List infer)) (input1 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let infer_t : infer := «exec:2»; (let «tail:0» : (_root_.List infer) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeId_t : typeId := «exec:4»; (let «tail:1» : (_root_.List typeId) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String infer)), SpecTecCall.«$resolve_constraint:case_3:iter:3» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String infer))) => (let «tail:2» : (_root_.List (pair _root_.String infer)) := «exec:5»; (.pure (((((pair.«% ':' %» typeId_t infer_t) : (pair typeId infer)) :: «tail:2») : (_root_.List (pair _root_.String infer)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$resolve_constraint:case_3:iter:3_clauses» (input0 : (_root_.List infer)) (input1 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$resolve_constraint:case_3:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$resolve_constraint:case_3:iter:3:clause:1»  input0 input1)]


noncomputable def «$resolve_constraint:case_3:pattern-iter:6:clause:0» (input0 : (_root_.List (pair _root_.String typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List typeIR)), ([] : (_root_.List typeId))) : ((_root_.List typeIR) × (_root_.List typeId))))) | _ :: _ => .unmatch)


noncomputable def «$resolve_constraint:case_3:pattern-iter:6:clause:1» (input0 : (_root_.List (pair _root_.String typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let typeId : SpecTec.typeId := «exec:3»; (let typeIR_t : typeIR := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair _root_.String typeIR)) := «exec:1»; (.bind (.call ⟨((_root_.List typeIR) × (_root_.List SpecTec.typeId)), SpecTecCall.«$resolve_constraint:case_3:pattern-iter:6» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List typeIR) × (_root_.List SpecTec.typeId))) => (let «pattern-tail:1» : (_root_.List typeIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.typeId) := («exec:5»).2; (.pure ((((typeIR_t :: «pattern-tail:1»), (typeId :: «pattern-tail:2»)) : ((_root_.List typeIR) × (_root_.List SpecTec.typeId))))))))))))) | [] => .unmatch)


noncomputable def «$resolve_constraint:case_3:pattern-iter:6_clauses» (input0 : (_root_.List (pair _root_.String typeIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$resolve_constraint:case_3:pattern-iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («$resolve_constraint:case_3:pattern-iter:6:clause:1»  input0)]


noncomputable def «$resolve_constraint:case_3:iter:8:clause:0» (input0 : (_root_.List typeId)) (input1 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$resolve_constraint:case_3:iter:8:clause:1» (input0 : (_root_.List SpecTec.typeId)) (input1 : (_root_.List SpecTec.typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeId_t : SpecTec.typeId := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeId) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeId : SpecTec.typeId := «exec:4»; (let «tail:1» : (_root_.List SpecTec.typeId) := «exec:3»; (.bind (.guard (typeId_t = typeId)) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$resolve_constraint:case_3:iter:8» «tail:0» «tail:1»⟩) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$resolve_constraint:case_3:iter:8_clauses» (input0 : (_root_.List typeId)) (input1 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$resolve_constraint:case_3:iter:8:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$resolve_constraint:case_3:iter:8:clause:1»  input0 input1)]


noncomputable def «$resolve_constraint:case_3:iter:9:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$resolve_constraint:case_3:iter:9:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_t : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeId_t : typeId := «exec:4»; (let «tail:1» : (_root_.List typeId) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$resolve_constraint:case_3:iter:9» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» typeId_t typeIR_t) : (pair typeId typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$resolve_constraint:case_3:iter:9_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$resolve_constraint:case_3:iter:9:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$resolve_constraint:case_3:iter:9:clause:1»  input0 input1)]


noncomputable def «$callableId_IR:case_1:iter:0:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List parameterInitializerOptIR)), (([] : (_root_.List typeIR)), ([] : (_root_.List id)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))))) | _ :: _ => .unmatch)


noncomputable def «$callableId_IR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (match parameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let _typeIR : typeIR := «exec:5»; (let id : SpecTec.id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List SpecTec.id))))), SpecTecCall.«$callableId_IR:case_1:iter:0» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List SpecTec.id)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List parameterInitializerOptIR) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List typeIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List SpecTec.id) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_parameterInitializerOptIR :: «tail:3»), ((_typeIR :: «tail:4»), (id :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List SpecTec.id))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «$callableId_IR:case_1:iter:0_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$callableId_IR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$callableId_IR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$callableId_IR:clause:0» (input0 : SpecTec.nameIR) (input1 : parameterListIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (let «parameterIR*» : (_root_.List parameterIR) := input1; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))), SpecTecCall.«$callableId_IR:case_1:iter:0» «parameterIR*»⟩) (fun («exec:1» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))) => (let «_annotationList*» : (_root_.List annotationList) := («exec:1»).1; (let «_direction*» : (_root_.List direction) := ((«exec:1»).2).1; (let «_parameterInitializerOptIR*» : (_root_.List parameterInitializerOptIR) := (((«exec:1»).2).2).1; (let «_typeIR*» : (_root_.List typeIR) := ((((«exec:1»).2).2).2).1; (let «id*» : (_root_.List id) := ((((«exec:1»).2).2).2).2; (.pure ((((callTargetId.«% `( % `)» nameIR «id*») : callTargetId) : callableId))))))))))))


noncomputable def «$callableId_IR_clauses» (input0 : nameIR) (input1 : parameterListIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$callableId_IR:clause:0»  input0 input1)]


noncomputable def «$parameterListIR_of_actionDef:clause:0» (input0 : actionDef) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% ACTION % `( % `) %» «exec:1» «exec:2» «exec:3» «exec:4» => (let annotationList : SpecTec.annotationList := «exec:1»; (let _nameIR : nameIR := «exec:2»; (let parameterListIR : SpecTec.parameterListIR := «exec:3»; (let _blockStatementIR : blockStatementIR := «exec:4»; (.pure ((parameterListIR : (_root_.List parameterIR)))))))))


noncomputable def «$parameterListIR_of_actionDef_clauses» (input0 : actionDef) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$parameterListIR_of_actionDef:clause:0»  input0)]


noncomputable def «$parameterListIR_of_definedFunctionDef:clause:0» (input0 : definedFunctionDef) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«FUNCTION % `< % `> `( % `) %» «exec:1» «exec:2» «exec:3» «exec:4» => (let _nameIR : nameIR := «exec:1»; (let _typeParameterListIR : typeParameterListIR := «exec:2»; (let parameterListIR : SpecTec.parameterListIR := «exec:3»; (let _blockStatementIR : blockStatementIR := «exec:4»; (.pure ((parameterListIR : (_root_.List parameterIR)))))))))


noncomputable def «$parameterListIR_of_definedFunctionDef_clauses» (input0 : definedFunctionDef) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$parameterListIR_of_definedFunctionDef:clause:0»  input0)]


noncomputable def «$parameterListIR_of_externFunctionDef:clause:0» (input0 : externFunctionDef) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«EXTERN_FUNCTION % `< % `> `( % `)» «exec:1» «exec:2» «exec:3» => (let _nameIR : nameIR := «exec:1»; (let _typeParameterListIR : typeParameterListIR := «exec:2»; (let parameterListIR : SpecTec.parameterListIR := «exec:3»; (.pure ((parameterListIR : (_root_.List parameterIR))))))))


noncomputable def «$parameterListIR_of_externFunctionDef_clauses» (input0 : externFunctionDef) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$parameterListIR_of_externFunctionDef:clause:0»  input0)]


noncomputable def «$parameterListIR_of_tableApplyMethodDef:clause:0» (input0 : tableApplyMethodDef) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«TABLE_APPLY `{ % `}» «exec:1» => (let _tablePropertyListIR : tablePropertyListIR := «exec:1»; (.pure ((([] : (_root_.List parameterIR)) : (_root_.List parameterIR))))))


noncomputable def «$parameterListIR_of_tableApplyMethodDef_clauses» (input0 : tableApplyMethodDef) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$parameterListIR_of_tableApplyMethodDef:clause:0»  input0)]

end SpecTec
