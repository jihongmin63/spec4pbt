import SpecTecDecl0212

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$resolve_inference:case_1:iter:4:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$resolve_inference:case_1:iter:4:clause:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List SpecTec.typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_resolved : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeId : SpecTec.typeId := «exec:4»; (let «tail:1» : (_root_.List SpecTec.typeId) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$resolve_inference:case_1:iter:4» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» typeId typeIR_resolved) : (pair SpecTec.typeId typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$resolve_inference:case_1:iter:4_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$resolve_inference:case_1:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$resolve_inference:case_1:iter:4:clause:1»  input0 input1)]


noncomputable def «$gen_constraint_pair:case_13:iter:2:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List id)), (([] : (_root_.List parameterInitializerOptIR)), (([] : (_root_.List direction)), ([] : (_root_.List typeIR)))))) : ((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR)))))))) | _ :: _ => .unmatch)


noncomputable def «$gen_constraint_pair:case_13:iter:2:clause:1» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR_param : parameterIR := «exec:2»; (let «tail:0» : (_root_.List parameterIR) := «exec:1»; (match parameterIR_param with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let direction : SpecTec.direction := «exec:4»; (let typeIR_param : typeIR := «exec:5»; (let _id : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List SpecTec.direction) × (_root_.List typeIR))))), SpecTecCall.«$gen_constraint_pair:case_13:iter:2» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List SpecTec.direction) × (_root_.List typeIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List id) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List parameterInitializerOptIR) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List SpecTec.direction) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List typeIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_id :: «tail:2»), ((_parameterInitializerOptIR :: «tail:3»), ((direction :: «tail:4»), (typeIR_param :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List SpecTec.direction) × (_root_.List typeIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «$gen_constraint_pair:case_13:iter:2_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$gen_constraint_pair:case_13:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$gen_constraint_pair:case_13:iter:2:clause:1»  input0)]


noncomputable def «$gen_constraint_pair:case_13:iter:3:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List id)), (([] : (_root_.List parameterInitializerOptIR)), (([] : (_root_.List direction)), ([] : (_root_.List typeIR)))))) : ((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR)))))))) | _ :: _ => .unmatch)


noncomputable def «$gen_constraint_pair:case_13:iter:3:clause:1» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR_arg : parameterIR := «exec:2»; (let «tail:0» : (_root_.List parameterIR) := «exec:1»; (match parameterIR_arg with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList' : annotationList := «exec:3»; (let direction' : direction := «exec:4»; (let typeIR_arg : typeIR := «exec:5»; (let _id' : id := «exec:6»; (let _parameterInitializerOptIR' : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR))))), SpecTecCall.«$gen_constraint_pair:case_13:iter:3» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List id) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List parameterInitializerOptIR) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List direction) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List typeIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList' :: «tail:1»), ((_id' :: «tail:2»), ((_parameterInitializerOptIR' :: «tail:3»), ((direction' :: «tail:4»), (typeIR_arg :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «$gen_constraint_pair:case_13:iter:3_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$gen_constraint_pair:case_13:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$gen_constraint_pair:case_13:iter:3:clause:1»  input0)]


noncomputable def «$gen_constraint_pair:case_13:iter:4:clause:0» (input0 : (_root_.List direction)) (input1 : (_root_.List direction)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$gen_constraint_pair:case_13:iter:4:clause:1» (input0 : (_root_.List SpecTec.direction)) (input1 : (_root_.List SpecTec.direction)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let direction : SpecTec.direction := «exec:2»; (let «tail:0» : (_root_.List SpecTec.direction) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let direction' : SpecTec.direction := «exec:4»; (let «tail:1» : (_root_.List SpecTec.direction) := «exec:3»; (.bind (.guard (direction = direction')) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$gen_constraint_pair:case_13:iter:4» «tail:0» «tail:1»⟩) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$gen_constraint_pair:case_13:iter:4_clauses» (input0 : (_root_.List direction)) (input1 : (_root_.List direction)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$gen_constraint_pair:case_13:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$gen_constraint_pair:case_13:iter:4:clause:1»  input0 input1)]


noncomputable def «$gen_constraint_pair:case_14:iter:2:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List id)), (([] : (_root_.List parameterInitializerOptIR)), (([] : (_root_.List direction)), ([] : (_root_.List typeIR)))))) : ((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR)))))))) | _ :: _ => .unmatch)


noncomputable def «$gen_constraint_pair:case_14:iter:2:clause:1» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR_param : parameterIR := «exec:2»; (let «tail:0» : (_root_.List parameterIR) := «exec:1»; (match parameterIR_param with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let direction : SpecTec.direction := «exec:4»; (let typeIR_param : typeIR := «exec:5»; (let _id : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List SpecTec.direction) × (_root_.List typeIR))))), SpecTecCall.«$gen_constraint_pair:case_14:iter:2» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List SpecTec.direction) × (_root_.List typeIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List id) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List parameterInitializerOptIR) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List SpecTec.direction) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List typeIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_id :: «tail:2»), ((_parameterInitializerOptIR :: «tail:3»), ((direction :: «tail:4»), (typeIR_param :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List SpecTec.direction) × (_root_.List typeIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «$gen_constraint_pair:case_14:iter:2_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$gen_constraint_pair:case_14:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$gen_constraint_pair:case_14:iter:2:clause:1»  input0)]


noncomputable def «$gen_constraint_pair:case_14:iter:3:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List id)), (([] : (_root_.List parameterInitializerOptIR)), (([] : (_root_.List direction)), ([] : (_root_.List typeIR)))))) : ((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR)))))))) | _ :: _ => .unmatch)


noncomputable def «$gen_constraint_pair:case_14:iter:3:clause:1» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR_arg : parameterIR := «exec:2»; (let «tail:0» : (_root_.List parameterIR) := «exec:1»; (match parameterIR_arg with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList' : annotationList := «exec:3»; (let direction' : direction := «exec:4»; (let typeIR_arg : typeIR := «exec:5»; (let _id' : id := «exec:6»; (let _parameterInitializerOptIR' : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR))))), SpecTecCall.«$gen_constraint_pair:case_14:iter:3» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List id) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List parameterInitializerOptIR) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List direction) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List typeIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList' :: «tail:1»), ((_id' :: «tail:2»), ((_parameterInitializerOptIR' :: «tail:3»), ((direction' :: «tail:4»), (typeIR_arg :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «$gen_constraint_pair:case_14:iter:3_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$gen_constraint_pair:case_14:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$gen_constraint_pair:case_14:iter:3:clause:1»  input0)]


noncomputable def «$gen_constraint_pair:case_14:iter:4:clause:0» (input0 : (_root_.List direction)) (input1 : (_root_.List direction)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$gen_constraint_pair:case_14:iter:4:clause:1» (input0 : (_root_.List SpecTec.direction)) (input1 : (_root_.List SpecTec.direction)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let direction : SpecTec.direction := «exec:2»; (let «tail:0» : (_root_.List SpecTec.direction) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let direction' : SpecTec.direction := «exec:4»; (let «tail:1» : (_root_.List SpecTec.direction) := «exec:3»; (.bind (.guard (direction = direction')) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$gen_constraint_pair:case_14:iter:4» «tail:0» «tail:1»⟩) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$gen_constraint_pair:case_14:iter:4_clauses» (input0 : (_root_.List direction)) (input1 : (_root_.List direction)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$gen_constraint_pair:case_14:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$gen_constraint_pair:case_14:iter:4:clause:1»  input0 input1)]


noncomputable def «$resolve_constraint:case_2:pattern-iter:0:clause:0» (input0 : (_root_.List (pair _root_.String infer))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List infer)), ([] : (_root_.List typeId))) : ((_root_.List infer) × (_root_.List typeId))))) | _ :: _ => .unmatch)


noncomputable def «$resolve_constraint:case_2:pattern-iter:0:clause:1» (input0 : (_root_.List (pair _root_.String infer))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let typeId_t : typeId := «exec:3»; (let infer_t : infer := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair _root_.String infer)) := «exec:1»; (.bind (.call ⟨((_root_.List infer) × (_root_.List typeId)), SpecTecCall.«$resolve_constraint:case_2:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List infer) × (_root_.List typeId))) => (let «pattern-tail:1» : (_root_.List infer) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List typeId) := («exec:5»).2; (.pure ((((infer_t :: «pattern-tail:1»), (typeId_t :: «pattern-tail:2»)) : ((_root_.List infer) × (_root_.List typeId))))))))))))) | [] => .unmatch)


noncomputable def «$resolve_constraint:case_2:pattern-iter:0_clauses» (input0 : (_root_.List (pair _root_.String infer))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$resolve_constraint:case_2:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$resolve_constraint:case_2:pattern-iter:0:clause:1»  input0)]


noncomputable def «$resolve_constraint:case_2:iter:2:clause:0» (input0 : (_root_.List infer)) (input1 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String infer))) : (_root_.List (pair _root_.String infer))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$resolve_constraint:case_2:iter:2:clause:1» (input0 : (_root_.List infer)) (input1 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let infer_t : infer := «exec:2»; (let «tail:0» : (_root_.List infer) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeId_t : typeId := «exec:4»; (let «tail:1» : (_root_.List typeId) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String infer)), SpecTecCall.«$resolve_constraint:case_2:iter:2» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String infer))) => (let «tail:2» : (_root_.List (pair _root_.String infer)) := «exec:5»; (.pure (((((pair.«% ':' %» typeId_t infer_t) : (pair typeId infer)) :: «tail:2») : (_root_.List (pair _root_.String infer)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$resolve_constraint:case_2:iter:2_clauses» (input0 : (_root_.List infer)) (input1 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$resolve_constraint:case_2:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$resolve_constraint:case_2:iter:2:clause:1»  input0 input1)]


noncomputable def «$resolve_constraint:case_2:pattern-iter:5:clause:0» (input0 : (_root_.List (pair _root_.String typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List typeIR)), ([] : (_root_.List typeId))) : ((_root_.List typeIR) × (_root_.List typeId))))) | _ :: _ => .unmatch)


noncomputable def «$resolve_constraint:case_2:pattern-iter:5:clause:1» (input0 : (_root_.List (pair _root_.String typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let typeId : SpecTec.typeId := «exec:3»; (let typeIR_t : typeIR := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair _root_.String typeIR)) := «exec:1»; (.bind (.call ⟨((_root_.List typeIR) × (_root_.List SpecTec.typeId)), SpecTecCall.«$resolve_constraint:case_2:pattern-iter:5» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List typeIR) × (_root_.List SpecTec.typeId))) => (let «pattern-tail:1» : (_root_.List typeIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.typeId) := («exec:5»).2; (.pure ((((typeIR_t :: «pattern-tail:1»), (typeId :: «pattern-tail:2»)) : ((_root_.List typeIR) × (_root_.List SpecTec.typeId))))))))))))) | [] => .unmatch)


noncomputable def «$resolve_constraint:case_2:pattern-iter:5_clauses» (input0 : (_root_.List (pair _root_.String typeIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$resolve_constraint:case_2:pattern-iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («$resolve_constraint:case_2:pattern-iter:5:clause:1»  input0)]


noncomputable def «$resolve_constraint:case_2:iter:7:clause:0» (input0 : (_root_.List typeId)) (input1 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$resolve_constraint:case_2:iter:7:clause:1» (input0 : (_root_.List SpecTec.typeId)) (input1 : (_root_.List SpecTec.typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeId_t : SpecTec.typeId := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeId) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeId : SpecTec.typeId := «exec:4»; (let «tail:1» : (_root_.List SpecTec.typeId) := «exec:3»; (.bind (.guard (typeId_t = typeId)) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$resolve_constraint:case_2:iter:7» «tail:0» «tail:1»⟩) (fun («exec:5» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch))) | [] => .unmatch)

end SpecTec
