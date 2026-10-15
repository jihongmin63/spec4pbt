import SpecTecDecl0204

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Decl_ok:headerUnionTypeDeclaration:iter:13_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:headerUnionTypeDeclaration:iter:13:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Decl_ok:headerUnionTypeDeclaration:iter:13:clause:1»  input0 input1 input2)]


noncomputable def «Decl_ok:packageTypeDeclaration:iter:3:clause:0» (input0 : (_root_.List constructorParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List id)), (([] : (_root_.List parameterInitializerOptIR)), ([] : (_root_.List typeIR)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:packageTypeDeclaration:iter:3:clause:1» (input0 : (_root_.List SpecTec.constructorParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let constructorParameterIR : SpecTec.constructorParameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.constructorParameterIR) := «exec:1»; (match constructorParameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let typeIR_package_inner : typeIR := «exec:5»; (let _id : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR))))), SpecTecCall.«Decl_ok:packageTypeDeclaration:iter:3» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List id) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List parameterInitializerOptIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List typeIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_id :: «tail:3»), ((_parameterInitializerOptIR :: «tail:4»), (typeIR_package_inner :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:packageTypeDeclaration:iter:3_clauses» (input0 : (_root_.List constructorParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:packageTypeDeclaration:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:packageTypeDeclaration:iter:3:clause:1»  input0)]


noncomputable def «CallableType_ok:externMethodTypeIR:pattern-iter:3:clause:0» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List callableId)), ([] : (_root_.List externMethodTypeDefIR))) : ((_root_.List callableId) × (_root_.List externMethodTypeDefIR))))) | _ :: _ => .unmatch)


noncomputable def «CallableType_ok:externMethodTypeIR:pattern-iter:3:clause:1» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let callableId_extern : callableId := «exec:3»; (let externMethodTypeDefIR_extern : externMethodTypeDefIR := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId externMethodTypeDefIR)) := «exec:1»; (.bind (.call ⟨((_root_.List callableId) × (_root_.List externMethodTypeDefIR)), SpecTecCall.«CallableType_ok:externMethodTypeIR:pattern-iter:3» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List callableId) × (_root_.List externMethodTypeDefIR))) => (let «pattern-tail:1» : (_root_.List callableId) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List externMethodTypeDefIR) := («exec:5»).2; (.pure ((((callableId_extern :: «pattern-tail:1»), (externMethodTypeDefIR_extern :: «pattern-tail:2»)) : ((_root_.List callableId) × (_root_.List externMethodTypeDefIR))))))))))))) | [] => .unmatch)


noncomputable def «CallableType_ok:externMethodTypeIR:pattern-iter:3_clauses» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableType_ok:externMethodTypeIR:pattern-iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («CallableType_ok:externMethodTypeIR:pattern-iter:3:clause:1»  input0)]


noncomputable def «CallableType_ok:externMethodTypeIR:iter:6:clause:0» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId externMethodTypeDefIR))) : (_root_.List (pair callTargetId externMethodTypeDefIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «CallableType_ok:externMethodTypeIR:iter:6:clause:1» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let callableId_extern : callableId := «exec:2»; (let «tail:0» : (_root_.List callableId) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let externMethodTypeDefIR_extern : externMethodTypeDefIR := «exec:4»; (let «tail:1» : (_root_.List externMethodTypeDefIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId externMethodTypeDefIR)), SpecTecCall.«CallableType_ok:externMethodTypeIR:iter:6» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId externMethodTypeDefIR))) => (let «tail:2» : (_root_.List (pair callTargetId externMethodTypeDefIR)) := «exec:5»; (.pure (((((pair.«% ':' %» callableId_extern externMethodTypeDefIR_extern) : (pair callTargetId externMethodTypeDefIR)) :: «tail:2») : (_root_.List (pair callTargetId externMethodTypeDefIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «CallableType_ok:externMethodTypeIR:iter:6_clauses» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableType_ok:externMethodTypeIR:iter:6:clause:0»  input0 input1), fun (_ : _root_.Unit) => («CallableType_ok:externMethodTypeIR:iter:6:clause:1»  input0 input1)]


noncomputable def «CallableType_ok:parserApplyMethodTypeIR:iter:3:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List parameterInitializerOptIR)), (([] : (_root_.List typeIR)), ([] : (_root_.List id)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))))) | _ :: _ => .unmatch)


noncomputable def «CallableType_ok:parserApplyMethodTypeIR:iter:3:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (match parameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let _typeIR : typeIR := «exec:5»; (let id_param : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))), SpecTecCall.«CallableType_ok:parserApplyMethodTypeIR:iter:3» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List parameterInitializerOptIR) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List typeIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List id) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_parameterInitializerOptIR :: «tail:3»), ((_typeIR :: «tail:4»), (id_param :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «CallableType_ok:parserApplyMethodTypeIR:iter:3_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableType_ok:parserApplyMethodTypeIR:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («CallableType_ok:parserApplyMethodTypeIR:iter:3:clause:1»  input0)]


noncomputable def «CallableType_ok:controlApplyMethodTypeIR:iter:3:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List parameterInitializerOptIR)), (([] : (_root_.List typeIR)), ([] : (_root_.List id)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))))) | _ :: _ => .unmatch)


noncomputable def «CallableType_ok:controlApplyMethodTypeIR:iter:3:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (match parameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let _typeIR : typeIR := «exec:5»; (let id_param : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))), SpecTecCall.«CallableType_ok:controlApplyMethodTypeIR:iter:3» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List parameterInitializerOptIR) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List typeIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List id) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_parameterInitializerOptIR :: «tail:3»), ((_typeIR :: «tail:4»), (id_param :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «CallableType_ok:controlApplyMethodTypeIR:iter:3_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableType_ok:controlApplyMethodTypeIR:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («CallableType_ok:controlApplyMethodTypeIR:iter:3:clause:1»  input0)]


noncomputable def «$chain_casts':clause:0» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_cur : typeIR := input0; (let «typeIR*» : (_root_.List typeIR) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeIR*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure (((typeIR_cur, ([] : (_root_.List typeIR))) : (typeIR × (_root_.List typeIR)))))))))


noncomputable def «$chain_casts':clause:1» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_cur : typeIR := input0; (let «typeIR*» : (_root_.List typeIR) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «typeIR*» with | «exec:2» :: «exec:1» => (let typeIR_h : typeIR := «exec:2»; (let «typeIR_t*» : (_root_.List typeIR) := «exec:1»; (.pure (((typeIR_h, «typeIR_t*») : (typeIR × (_root_.List typeIR))))))) | [] => .unmatch)))))


noncomputable def «$chain_casts'_clauses» (input0 : typeIR) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$chain_casts':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$chain_casts':clause:1»  input0 input1)]


noncomputable def «$chain_casts:case_2:iter:0:clause:0» (input0 : (_root_.List (_root_.List typeIR))) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((([] : (_root_.List (_root_.List typeIR))), ([] : (_root_.List typeIR))) : ((_root_.List (_root_.List typeIR)) × (_root_.List typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$chain_casts:case_2:iter:0:clause:1» (input0 : (_root_.List (_root_.List typeIR))) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let «typeIR_chain*» : (_root_.List typeIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.List typeIR)) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeIR_cur : typeIR := «exec:4»; (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(typeIR × (_root_.List typeIR)), SpecTecCall.«$chain_casts'» typeIR_cur «typeIR_chain*»⟩) (fun («exec:5» : (typeIR × (_root_.List typeIR))) => (let «eval:1» : (typeIR × (_root_.List typeIR)) := «exec:5»; (let typeIR_next : typeIR := («eval:1»).1; (let «typeIR_chain_rest*» : (_root_.List typeIR) := («eval:1»).2; (.bind (.call ⟨((_root_.List (_root_.List typeIR)) × (_root_.List typeIR)), SpecTecCall.«$chain_casts:case_2:iter:0» «tail:0» «tail:1»⟩) (fun («exec:6» : ((_root_.List (_root_.List typeIR)) × (_root_.List typeIR))) => (let «tail:2» : (_root_.List (_root_.List typeIR)) := («exec:6»).1; (let «tail:3» : (_root_.List typeIR) := («exec:6»).2; (.pure ((((«typeIR_chain_rest*» :: «tail:2»), (typeIR_next :: «tail:3»)) : ((_root_.List (_root_.List typeIR)) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$chain_casts:case_2:iter:0_clauses» (input0 : (_root_.List (_root_.List typeIR))) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$chain_casts:case_2:iter:0:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$chain_casts:case_2:iter:0:clause:1»  input0 input1)]


noncomputable def «$chain_casts:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List (_root_.List typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «typeIR_cur*» : (_root_.List typeIR) := input0; (let «typeIR_chain**» : (_root_.List (_root_.List typeIR)) := input1; (match («$concat_» (X := typeIR) «typeIR_chain**») with | [] => (.pure ((([] : (_root_.List (_root_.List typeIR))) : (_root_.List (_root_.List typeIR))))) | _ :: _ => .unmatch)))


noncomputable def «$chain_casts:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List (_root_.List typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «typeIR_cur*» : (_root_.List typeIR) := input0; (let «typeIR_chain**» : (_root_.List (_root_.List typeIR)) := input1; (.bind (.guard ((([] : (_root_.List typeIR)) ≠ («$concat_» (X := typeIR) «typeIR_chain**»)))) (fun (_ : Unit) => (.bind (.guard ((_root_.List.length «typeIR_cur*») = (_root_.List.length «typeIR_chain**»))) (fun (_ : Unit) => (.bind (.call ⟨((_root_.List (_root_.List typeIR)) × (_root_.List typeIR)), SpecTecCall.«$chain_casts:case_2:iter:0» «typeIR_chain**» «typeIR_cur*»⟩) (fun («exec:1» : ((_root_.List (_root_.List typeIR)) × (_root_.List typeIR))) => (let «typeIR_chain_rest**» : (_root_.List (_root_.List typeIR)) := («exec:1»).1; (let «typeIR_next*» : (_root_.List typeIR) := («exec:1»).2; (.bind (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«$chain_casts» «typeIR_next*» «typeIR_chain_rest**»⟩) (fun («exec:2» : (_root_.List (_root_.List typeIR))) => (let «eval:2» : (_root_.List (_root_.List typeIR)) := «exec:2»; (.pure (((«typeIR_next*» :: «eval:2») : (_root_.List (_root_.List typeIR))))))))))))))))))


noncomputable def «$chain_casts_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List (_root_.List typeIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$chain_casts:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$chain_casts:clause:1»  input0 input1)]


noncomputable def «$chain_casts_sequenceTypeIR:case_1:iter:1:clause:0» (input0 : (_root_.List (_root_.List typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «$chain_casts_sequenceTypeIR:case_1:iter:1:clause:1» (input0 : (_root_.List (_root_.List typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let «typeIR_cast_step*» : (_root_.List typeIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.List typeIR)) := «exec:1»; (let typeIR_cast_agg : typeIR := ((typeIR.«SEQ `< % `>» «typeIR_cast_step*») : typeIR); (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$chain_casts_sequenceTypeIR:case_1:iter:1» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((typeIR_cast_agg :: «tail:1») : (_root_.List typeIR)))))))))) | [] => .unmatch)


noncomputable def «$chain_casts_sequenceTypeIR:case_1:iter:1_clauses» (input0 : (_root_.List (_root_.List typeIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$chain_casts_sequenceTypeIR:case_1:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$chain_casts_sequenceTypeIR:case_1:iter:1:clause:1»  input0)]


noncomputable def «$chain_casts_sequenceTypeIR:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List (_root_.List typeIR))) (input2 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «typeIR_a*» : (_root_.List typeIR) := input0; (let «typeIR_cast_elem**» : (_root_.List (_root_.List typeIR)) := input1; (let typeIR_b : typeIR := input2; (.bind (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«$chain_casts» «typeIR_a*» «typeIR_cast_elem**»⟩) (fun («exec:1» : (_root_.List (_root_.List typeIR))) => (let «eval:0» : (_root_.List (_root_.List typeIR)) := «exec:1»; (let «typeIR_cast_step**» : (_root_.List (_root_.List typeIR)) := «eval:0»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$chain_casts_sequenceTypeIR:case_1:iter:1» «typeIR_cast_step**»⟩) (fun («exec:2» : (_root_.List typeIR)) => (let «typeIR_cast_agg*» : (_root_.List typeIR) := «exec:2»; (.pure (((«typeIR_cast_agg*» ++ ([typeIR_b] : (_root_.List typeIR))) : (_root_.List typeIR))))))))))))))


noncomputable def «$chain_casts_sequenceTypeIR_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List (_root_.List typeIR))) (input2 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$chain_casts_sequenceTypeIR:clause:0»  input0 input1 input2)]


noncomputable def «$chain_casts_sequenceTypeIR_default:case_1:iter:1:clause:0» (input0 : (_root_.List (_root_.List typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «$chain_casts_sequenceTypeIR_default:case_1:iter:1:clause:1» (input0 : (_root_.List (_root_.List typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let «typeIR_cast_step*» : (_root_.List typeIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.List typeIR)) := «exec:1»; (let typeIR_cast_agg : typeIR := ((typeIR.«SEQ `< % ',' '...' `>» «typeIR_cast_step*») : typeIR); (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$chain_casts_sequenceTypeIR_default:case_1:iter:1» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((typeIR_cast_agg :: «tail:1») : (_root_.List typeIR)))))))))) | [] => .unmatch)

end SpecTec
