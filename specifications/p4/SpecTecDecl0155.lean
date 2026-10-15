import SpecTecDecl0154

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$default:case_14:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_f : typeIR := «exec:4»; (let id_f : id := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$default:case_14:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List id) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((id_f :: «pattern-tail:2»), (typeIR_f :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$default:case_14:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$default:case_14:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$default:case_14:pattern-iter:1:clause:1»  input0)]


noncomputable def «$default:case_15:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List id)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$default:case_15:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_f : typeIR := «exec:4»; (let id_f : id := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$default:case_15:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List id) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((id_f :: «pattern-tail:2»), (typeIR_f :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$default:case_15:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$default:case_15:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$default:case_15:pattern-iter:1:clause:1»  input0)]


noncomputable def «$cast_sequence:case_7:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$cast_sequence:case_7:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$cast_sequence:case_7:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((nameIR_field :: «pattern-tail:2»), (typeIR_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$cast_sequence:case_7:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_sequence:case_7:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$cast_sequence:case_7:pattern-iter:1:clause:1»  input0)]


noncomputable def «$cast_sequence:case_8:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$cast_sequence:case_8:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$cast_sequence:case_8:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((nameIR_field :: «pattern-tail:2»), (typeIR_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$cast_sequence:case_8:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_sequence:case_8:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$cast_sequence:case_8:pattern-iter:1:clause:1»  input0)]


noncomputable def «$cast_sequence:case_13:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$cast_sequence:case_13:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$cast_sequence:case_13:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((nameIR_field :: «pattern-tail:2»), (typeIR_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$cast_sequence:case_13:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_sequence:case_13:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$cast_sequence:case_13:pattern-iter:1:clause:1»  input0)]


noncomputable def «$cast_sequence:case_14:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$cast_sequence:case_14:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_field : typeIR := «exec:4»; (let nameIR_field : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$cast_sequence:case_14:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((nameIR_field :: «pattern-tail:2»), (typeIR_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$cast_sequence:case_14:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_sequence:case_14:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$cast_sequence:case_14:pattern-iter:1:clause:1»  input0)]


noncomputable def «$cast_record:case_1:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List id)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$cast_record:case_1:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_t_field : typeIR := «exec:4»; (let id_t_field : id := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$cast_record:case_1:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List id) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((id_t_field :: «pattern-tail:2»), (typeIR_t_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$cast_record:case_1:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_record:case_1:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$cast_record:case_1:pattern-iter:1:clause:1»  input0)]


noncomputable def «$cast_record:case_2:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List id)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$cast_record:case_2:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_t_field : typeIR := «exec:4»; (let id_t_field : id := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$cast_record:case_2:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List id) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((id_t_field :: «pattern-tail:2»), (typeIR_t_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$cast_record:case_2:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_record:case_2:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$cast_record:case_2:pattern-iter:1:clause:1»  input0)]


noncomputable def «$cast_record:case_3:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List id)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$cast_record:case_3:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_t_field : typeIR := «exec:4»; (let id_t_field : id := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$cast_record:case_3:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List id) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((id_t_field :: «pattern-tail:2»), (typeIR_t_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$cast_record:case_3:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_record:case_3:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$cast_record:case_3:pattern-iter:1:clause:1»  input0)]


noncomputable def «$cast_record:case_4:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List id)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$cast_record:case_4:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_t_field : typeIR := «exec:4»; (let id_t_field : id := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$cast_record:case_4:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List id) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((id_t_field :: «pattern-tail:2»), (typeIR_t_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$cast_record:case_4:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_record:case_4:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$cast_record:case_4:pattern-iter:1:clause:1»  input0)]


noncomputable def «$cast_record:case_5:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List id)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$cast_record:case_5:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_t_field : typeIR := «exec:4»; (let id_t_field : id := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$cast_record:case_5:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List id) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((id_t_field :: «pattern-tail:2»), (typeIR_t_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$cast_record:case_5:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_record:case_5:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$cast_record:case_5:pattern-iter:1:clause:1»  input0)]

end SpecTec
