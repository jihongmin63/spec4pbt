import SpecTecDecl0276

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$subst_typeIR':clause:24» (input0 : SpecTec.theta) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (let typeIR : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:recordTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$subst_typeIR':case_25:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.recordTypeIR := «exec:1»; (let recordTypeIR : SpecTec.recordTypeIR := «eval:0»; (.bind (.guard (((«exec:match:recordTypeIR:RECORD `{ % ',' '...' `}» recordTypeIR) = true))) (fun (_ : Unit) => (match recordTypeIR with | .«RECORD `{ % ',' '...' `}» «exec:2» => (let «eval:2» : (_root_.List fieldTypeIR) := «exec:2»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List SpecTec.typeIR))), SpecTecCall.«$subst_typeIR':case_25:pattern-iter:1» «eval:2»⟩) (fun («exec:3» : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List SpecTec.typeIR)))) => (let «annotationList*» : (_root_.List annotationList) := («exec:3»).1; (let «id_field*» : (_root_.List id) := ((«exec:3»).2).1; (let «typeIR_field*» : (_root_.List SpecTec.typeIR) := ((«exec:3»).2).2; (.bind (.call ⟨(_root_.List SpecTec.typeIR), SpecTecCall.«$subst_typeIR':case_25:iter:3» theta «typeIR_field*»⟩) (fun («exec:4» : (_root_.List SpecTec.typeIR)) => (let «typeIR_field_subst*» : (_root_.List SpecTec.typeIR) := «exec:4»; (.bind (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«$subst_typeIR':case_25:iter:5» «annotationList*» «id_field*» «typeIR_field_subst*»⟩) (fun («exec:5» : (_root_.List fieldTypeIR)) => (let «eval:6» : (_root_.List fieldTypeIR) := «exec:5»; (.pure ((((SpecTec.typeIR.«RECORD `{ % ',' '...' `}» «eval:6») : SpecTec.typeIR) : SpecTec.typeIR))))))))))))))) | _ => .unmatch))))) | none => .unmatch)))))


noncomputable def «$subst_typeIR':clause:25» (input0 : SpecTec.theta) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (let typeIR' : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:setTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$subst_typeIR':case_26:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : setTypeIR := «exec:1»; (match «eval:0» with | .«SET `< % `>» «exec:2» => (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$subst_typeIR'» theta typeIR⟩) (fun («exec:3» : SpecTec.typeIR) => (let «eval:1» : SpecTec.typeIR := «exec:3»; (let typeIR_subst : SpecTec.typeIR := «eval:1»; (.pure ((((SpecTec.typeIR.«SET `< % `>» typeIR_subst) : SpecTec.typeIR) : SpecTec.typeIR)))))))))) | none => .unmatch)))))


noncomputable def «$subst_typeIR':clause:26» (input0 : SpecTec.theta) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (let typeIR : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:tableMetadataTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$subst_typeIR':case_27:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.tableMetadataTypeIR := «exec:1»; (let tableMetadataTypeIR : SpecTec.tableMetadataTypeIR := «eval:0»; (.pure (((«cast:tableMetadataTypeIR:typeIR» tableMetadataTypeIR) : SpecTec.typeIR))))) | none => .unmatch)))))


noncomputable def «$subst_typeIR'_clauses» (input0 : theta) (input1 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:1»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:2»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:3»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:4»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:5»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:6»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:7»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:8»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:9»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:10»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:11»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:12»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:13»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:14»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:15»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:16»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:17»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:18»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:19»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:20»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:21»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:22»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:23»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:24»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:25»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':clause:26»  input0 input1)]


noncomputable def «$subst_typeIR':case_7:iter:1:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_typeIR':case_7:iter:1:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$subst_typeIR'» theta typeIR⟩) (fun («exec:3» : SpecTec.typeIR) => (let «eval:2» : SpecTec.typeIR := «exec:3»; (let typeIR_subst : SpecTec.typeIR := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.typeIR), SpecTecCall.«$subst_typeIR':case_7:iter:1» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.typeIR)) => (let «tail:1» : (_root_.List SpecTec.typeIR) := «exec:4»; (.pure (((typeIR_subst :: «tail:1») : (_root_.List SpecTec.typeIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_typeIR':case_7:iter:1_clauses» (input0 : theta) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_7:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':case_7:iter:1:clause:1»  input0 input1)]


noncomputable def «$subst_typeIR':case_10:iter:3:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeArgumentIR)) : (_root_.List typeArgumentIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_typeIR':case_10:iter:3:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (.bind (.call ⟨typeIR, SpecTecCall.«$subst_typeIR'» theta typeArgumentIR⟩) (fun («exec:3» : typeIR) => (let «eval:4» : typeIR := «exec:3»; (let typeArgumentIR_subst : SpecTec.typeArgumentIR := «eval:4»; (.bind (.call ⟨(_root_.List SpecTec.typeArgumentIR), SpecTecCall.«$subst_typeIR':case_10:iter:3» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.typeArgumentIR)) => (let «tail:1» : (_root_.List SpecTec.typeArgumentIR) := «exec:4»; (.pure (((typeArgumentIR_subst :: «tail:1») : (_root_.List SpecTec.typeArgumentIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_typeIR':case_10:iter:3_clauses» (input0 : theta) (input1 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_10:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':case_10:iter:3:clause:1»  input0 input1)]


noncomputable def «$subst_typeIR':case_10:iter:5:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_typeIR':case_10:iter:5:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeIR_field : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨typeIR, SpecTecCall.«$subst_typeIR'» theta typeIR_field⟩) (fun («exec:3» : typeIR) => (let «eval:6» : typeIR := «exec:3»; (let typeIR_field_subst : typeIR := «eval:6»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$subst_typeIR':case_10:iter:5» theta «tail:0»⟩) (fun («exec:4» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:4»; (.pure (((typeIR_field_subst :: «tail:1») : (_root_.List typeIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_typeIR':case_10:iter:5_clauses» (input0 : theta) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_10:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':case_10:iter:5:clause:1»  input0 input1)]


noncomputable def «$subst_typeIR':case_11:iter:3:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeArgumentIR)) : (_root_.List typeArgumentIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_typeIR':case_11:iter:3:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (.bind (.call ⟨typeIR, SpecTecCall.«$subst_typeIR'» theta typeArgumentIR⟩) (fun («exec:3» : typeIR) => (let «eval:4» : typeIR := «exec:3»; (let typeArgumentIR_subst : SpecTec.typeArgumentIR := «eval:4»; (.bind (.call ⟨(_root_.List SpecTec.typeArgumentIR), SpecTecCall.«$subst_typeIR':case_11:iter:3» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.typeArgumentIR)) => (let «tail:1» : (_root_.List SpecTec.typeArgumentIR) := «exec:4»; (.pure (((typeArgumentIR_subst :: «tail:1») : (_root_.List SpecTec.typeArgumentIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_typeIR':case_11:iter:3_clauses» (input0 : theta) (input1 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_11:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':case_11:iter:3:clause:1»  input0 input1)]


noncomputable def «$subst_typeIR':case_11:iter:5:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_typeIR':case_11:iter:5:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeIR_field : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨typeIR, SpecTecCall.«$subst_typeIR'» theta typeIR_field⟩) (fun («exec:3» : typeIR) => (let «eval:6» : typeIR := «exec:3»; (let typeIR_field_subst : typeIR := «eval:6»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$subst_typeIR':case_11:iter:5» theta «tail:0»⟩) (fun («exec:4» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:4»; (.pure (((typeIR_field_subst :: «tail:1») : (_root_.List typeIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_typeIR':case_11:iter:5_clauses» (input0 : theta) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_11:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':case_11:iter:5:clause:1»  input0 input1)]


noncomputable def «$subst_typeIR':case_12:iter:3:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeArgumentIR)) : (_root_.List typeArgumentIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_typeIR':case_12:iter:3:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (.bind (.call ⟨typeIR, SpecTecCall.«$subst_typeIR'» theta typeArgumentIR⟩) (fun («exec:3» : typeIR) => (let «eval:4» : typeIR := «exec:3»; (let typeArgumentIR_subst : SpecTec.typeArgumentIR := «eval:4»; (.bind (.call ⟨(_root_.List SpecTec.typeArgumentIR), SpecTecCall.«$subst_typeIR':case_12:iter:3» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.typeArgumentIR)) => (let «tail:1» : (_root_.List SpecTec.typeArgumentIR) := «exec:4»; (.pure (((typeArgumentIR_subst :: «tail:1») : (_root_.List SpecTec.typeArgumentIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_typeIR':case_12:iter:3_clauses» (input0 : theta) (input1 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_12:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':case_12:iter:3:clause:1»  input0 input1)]


noncomputable def «$subst_typeIR':case_12:iter:5:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_typeIR':case_12:iter:5:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeIR_field : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨typeIR, SpecTecCall.«$subst_typeIR'» theta typeIR_field⟩) (fun («exec:3» : typeIR) => (let «eval:6» : typeIR := «exec:3»; (let typeIR_field_subst : typeIR := «eval:6»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$subst_typeIR':case_12:iter:5» theta «tail:0»⟩) (fun («exec:4» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:4»; (.pure (((typeIR_field_subst :: «tail:1») : (_root_.List typeIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_typeIR':case_12:iter:5_clauses» (input0 : theta) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_12:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':case_12:iter:5:clause:1»  input0 input1)]


noncomputable def «$subst_typeIR':case_15:iter:3:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeArgumentIR)) : (_root_.List typeArgumentIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_typeIR':case_15:iter:3:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (.bind (.call ⟨typeIR, SpecTecCall.«$subst_typeIR'» theta typeArgumentIR⟩) (fun («exec:3» : typeIR) => (let «eval:4» : typeIR := «exec:3»; (let typeArgumentIR_subst : SpecTec.typeArgumentIR := «eval:4»; (.bind (.call ⟨(_root_.List SpecTec.typeArgumentIR), SpecTecCall.«$subst_typeIR':case_15:iter:3» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.typeArgumentIR)) => (let «tail:1» : (_root_.List SpecTec.typeArgumentIR) := «exec:4»; (.pure (((typeArgumentIR_subst :: «tail:1») : (_root_.List SpecTec.typeArgumentIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_typeIR':case_15:iter:3_clauses» (input0 : theta) (input1 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_15:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':case_15:iter:3:clause:1»  input0 input1)]


noncomputable def «$subst_typeIR':case_15:iter:5:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List callableTypeDefIR)) : (_root_.List callableTypeDefIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_typeIR':case_15:iter:5:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.externMethodTypeDefIR) := «exec:1»; (.bind (.call ⟨SpecTec.callableTypeDefIR, SpecTecCall.«$subst_callableTypeDefIR» theta («cast:externMethodTypeDefIR:callableTypeDefIR» externMethodTypeDefIR)⟩) (fun («exec:3» : SpecTec.callableTypeDefIR) => (let «eval:6» : SpecTec.callableTypeDefIR := «exec:3»; (let callableTypeDefIR : SpecTec.callableTypeDefIR := «eval:6»; (.bind (.call ⟨(_root_.List SpecTec.callableTypeDefIR), SpecTecCall.«$subst_typeIR':case_15:iter:5» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.callableTypeDefIR)) => (let «tail:1» : (_root_.List SpecTec.callableTypeDefIR) := «exec:4»; (.pure (((callableTypeDefIR :: «tail:1») : (_root_.List SpecTec.callableTypeDefIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_typeIR':case_15:iter:5_clauses» (input0 : theta) (input1 : (_root_.List externMethodTypeDefIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_15:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':case_15:iter:5:clause:1»  input0 input1)]


noncomputable def «$subst_typeIR':case_16:iter:1:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeArgumentIR)) : (_root_.List typeArgumentIR)))) | _ :: _ => .unmatch))

end SpecTec
