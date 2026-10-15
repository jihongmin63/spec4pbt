import SpecTecDecl0205

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$chain_casts_sequenceTypeIR_default:case_1:iter:1_clauses» (input0 : (_root_.List (_root_.List typeIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$chain_casts_sequenceTypeIR_default:case_1:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$chain_casts_sequenceTypeIR_default:case_1:iter:1:clause:1»  input0)]


noncomputable def «$chain_casts_sequenceTypeIR_default:clause:0» (input0 : (_root_.List typeIR)) (input1 : (_root_.List (_root_.List typeIR))) (input2 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «typeIR_a*» : (_root_.List typeIR) := input0; (let «typeIR_cast_elem**» : (_root_.List (_root_.List typeIR)) := input1; (let typeIR_b : typeIR := input2; (.bind (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«$chain_casts» «typeIR_a*» «typeIR_cast_elem**»⟩) (fun («exec:1» : (_root_.List (_root_.List typeIR))) => (let «eval:0» : (_root_.List (_root_.List typeIR)) := «exec:1»; (let «typeIR_cast_step**» : (_root_.List (_root_.List typeIR)) := «eval:0»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$chain_casts_sequenceTypeIR_default:case_1:iter:1» «typeIR_cast_step**»⟩) (fun («exec:2» : (_root_.List typeIR)) => (let «typeIR_cast_agg*» : (_root_.List typeIR) := «exec:2»; (.pure (((«typeIR_cast_agg*» ++ ([typeIR_b] : (_root_.List typeIR))) : (_root_.List typeIR))))))))))))))


noncomputable def «$chain_casts_sequenceTypeIR_default_clauses» (input0 : (_root_.List typeIR)) (input1 : (_root_.List (_root_.List typeIR))) (input2 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$chain_casts_sequenceTypeIR_default:clause:0»  input0 input1 input2)]


noncomputable def «$chain_casts_recordTypeIR:case_1:pattern-iter:0:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List id)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$chain_casts_recordTypeIR:case_1:pattern-iter:0:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let annotationList_a : annotationList := «exec:3»; (let typeIR_a : typeIR := «exec:4»; (let id_a : id := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$chain_casts_recordTypeIR:case_1:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List id) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((annotationList_a :: «pattern-tail:1»), ((id_a :: «pattern-tail:2»), (typeIR_a :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$chain_casts_recordTypeIR:case_1:pattern-iter:0_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$chain_casts_recordTypeIR:case_1:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$chain_casts_recordTypeIR:case_1:pattern-iter:0:clause:1»  input0)]


noncomputable def «$chain_casts_recordTypeIR:case_1:iter:3:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List (_root_.List typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «annotationList_a*» : (_root_.List annotationList) := input0; (let «id_a*» : (_root_.List id) := input1; (match input2 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)))


noncomputable def «$chain_casts_recordTypeIR:case_1:iter:3:clause:1» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List (_root_.List typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «annotationList_a*» : (_root_.List annotationList) := input0; (let «id_a*» : (_root_.List id) := input1; (match input2 with | «exec:2» :: «exec:1» => (let «typeIR_cast_step*» : (_root_.List typeIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.List typeIR)) := «exec:1»; (.bind (.guard ((((_root_.List.length «annotationList_a*») = (_root_.List.length «id_a*»)) ∧ ((_root_.List.length «id_a*») = (_root_.List.length «typeIR_cast_step*»))))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$chain_casts_recordTypeIR:case_1:iter:3» «annotationList_a*» «id_a*» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)))


noncomputable def «$chain_casts_recordTypeIR:case_1:iter:3_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List (_root_.List typeIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$chain_casts_recordTypeIR:case_1:iter:3:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$chain_casts_recordTypeIR:case_1:iter:3:clause:1»  input0 input1 input2)]


noncomputable def «$chain_casts_recordTypeIR:case_1:iter:5:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List fieldTypeIR)) : (_root_.List fieldTypeIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$chain_casts_recordTypeIR:case_1:iter:5:clause:1» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotationList_a : annotationList := «exec:2»; (let «tail:0» : (_root_.List annotationList) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let id_a : id := «exec:4»; (let «tail:1» : (_root_.List id) := «exec:3»; (match input2 with | «exec:6» :: «exec:5» => (let typeIR_cast_step : typeIR := «exec:6»; (let «tail:2» : (_root_.List typeIR) := «exec:5»; (.bind (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«$chain_casts_recordTypeIR:case_1:iter:5» «tail:0» «tail:1» «tail:2»⟩) (fun («exec:7» : (_root_.List fieldTypeIR)) => (let «tail:3» : (_root_.List fieldTypeIR) := «exec:7»; (.pure (((((fieldTypeIR.«% % % ';'» annotationList_a typeIR_cast_step id_a) : fieldTypeIR) :: «tail:3») : (_root_.List fieldTypeIR))))))))) | [] => .unmatch))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$chain_casts_recordTypeIR:case_1:iter:5_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$chain_casts_recordTypeIR:case_1:iter:5:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$chain_casts_recordTypeIR:case_1:iter:5:clause:1»  input0 input1 input2)]


noncomputable def «$chain_casts_recordTypeIR:case_1:iter:4:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List (_root_.List typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «annotationList_a*» : (_root_.List annotationList) := input0; (let «id_a*» : (_root_.List id) := input1; (match input2 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)))


noncomputable def «$chain_casts_recordTypeIR:case_1:iter:4:clause:1» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List (_root_.List typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «annotationList_a*» : (_root_.List annotationList) := input0; (let «id_a*» : (_root_.List id) := input1; (match input2 with | «exec:2» :: «exec:1» => (let «typeIR_cast_step*» : (_root_.List typeIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.List typeIR)) := «exec:1»; (.bind (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«$chain_casts_recordTypeIR:case_1:iter:5» «annotationList_a*» «id_a*» «typeIR_cast_step*»⟩) (fun («exec:3» : (_root_.List fieldTypeIR)) => (let «eval:6» : (_root_.List fieldTypeIR) := «exec:3»; (let typeIR_cast_agg : typeIR := ((typeIR.«RECORD `{ % `}» «eval:6») : typeIR); (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$chain_casts_recordTypeIR:case_1:iter:4» «annotationList_a*» «id_a*» «tail:0»⟩) (fun («exec:4» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:4»; (.pure (((typeIR_cast_agg :: «tail:1») : (_root_.List typeIR))))))))))))) | [] => .unmatch)))


noncomputable def «$chain_casts_recordTypeIR:case_1:iter:4_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List (_root_.List typeIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$chain_casts_recordTypeIR:case_1:iter:4:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$chain_casts_recordTypeIR:case_1:iter:4:clause:1»  input0 input1 input2)]


noncomputable def «$chain_casts_recordTypeIR:clause:0» (input0 : (_root_.List fieldTypeIR)) (input1 : (_root_.List (_root_.List typeIR))) (input2 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «eval:1» : (_root_.List fieldTypeIR) := input0; (let «typeIR_cast_elem**» : (_root_.List (_root_.List typeIR)) := input1; (let typeIR_b : typeIR := input2; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$chain_casts_recordTypeIR:case_1:pattern-iter:0» «eval:1»⟩) (fun («exec:1» : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))) => (let «annotationList_a*» : (_root_.List annotationList) := («exec:1»).1; (let «id_a*» : (_root_.List id) := ((«exec:1»).2).1; (let «typeIR_a*» : (_root_.List typeIR) := ((«exec:1»).2).2; (.bind (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«$chain_casts» «typeIR_a*» «typeIR_cast_elem**»⟩) (fun («exec:2» : (_root_.List (_root_.List typeIR))) => (let «eval:2» : (_root_.List (_root_.List typeIR)) := «exec:2»; (let «typeIR_cast_step**» : (_root_.List (_root_.List typeIR)) := «eval:2»; (.bind (.call ⟨_root_.Unit, SpecTecCall.«$chain_casts_recordTypeIR:case_1:iter:3» «annotationList_a*» «id_a*» «typeIR_cast_step**»⟩) (fun («exec:3» : _root_.Unit) => (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$chain_casts_recordTypeIR:case_1:iter:4» «annotationList_a*» «id_a*» «typeIR_cast_step**»⟩) (fun («exec:4» : (_root_.List typeIR)) => (let «typeIR_cast_agg*» : (_root_.List typeIR) := «exec:4»; (.pure (((«typeIR_cast_agg*» ++ ([typeIR_b] : (_root_.List typeIR))) : (_root_.List typeIR)))))))))))))))))))))


noncomputable def «$chain_casts_recordTypeIR_clauses» (input0 : (_root_.List fieldTypeIR)) (input1 : (_root_.List (_root_.List typeIR))) (input2 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$chain_casts_recordTypeIR:clause:0»  input0 input1 input2)]


noncomputable def «$chain_casts_recordTypeIR_default:case_1:pattern-iter:0:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List id)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$chain_casts_recordTypeIR_default:case_1:pattern-iter:0:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let annotationList_a : annotationList := «exec:3»; (let typeIR_a : typeIR := «exec:4»; (let id_a : id := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$chain_casts_recordTypeIR_default:case_1:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List id) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((annotationList_a :: «pattern-tail:1»), ((id_a :: «pattern-tail:2»), (typeIR_a :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$chain_casts_recordTypeIR_default:case_1:pattern-iter:0_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$chain_casts_recordTypeIR_default:case_1:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$chain_casts_recordTypeIR_default:case_1:pattern-iter:0:clause:1»  input0)]


noncomputable def «$chain_casts_recordTypeIR_default:case_1:iter:3:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List (_root_.List typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «annotationList_a*» : (_root_.List annotationList) := input0; (let «id_a*» : (_root_.List id) := input1; (match input2 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)))


noncomputable def «$chain_casts_recordTypeIR_default:case_1:iter:3:clause:1» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List (_root_.List typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «annotationList_a*» : (_root_.List annotationList) := input0; (let «id_a*» : (_root_.List id) := input1; (match input2 with | «exec:2» :: «exec:1» => (let «typeIR_cast_step*» : (_root_.List typeIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.List typeIR)) := «exec:1»; (.bind (.guard ((((_root_.List.length «annotationList_a*») = (_root_.List.length «id_a*»)) ∧ ((_root_.List.length «id_a*») = (_root_.List.length «typeIR_cast_step*»))))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$chain_casts_recordTypeIR_default:case_1:iter:3» «annotationList_a*» «id_a*» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)))


noncomputable def «$chain_casts_recordTypeIR_default:case_1:iter:3_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List (_root_.List typeIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$chain_casts_recordTypeIR_default:case_1:iter:3:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$chain_casts_recordTypeIR_default:case_1:iter:3:clause:1»  input0 input1 input2)]


noncomputable def «$chain_casts_recordTypeIR_default:case_1:iter:5:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List fieldTypeIR)) : (_root_.List fieldTypeIR)))) | _ :: _ => .unmatch) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$chain_casts_recordTypeIR_default:case_1:iter:5:clause:1» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let annotationList_a : annotationList := «exec:2»; (let «tail:0» : (_root_.List annotationList) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let id_a : id := «exec:4»; (let «tail:1» : (_root_.List id) := «exec:3»; (match input2 with | «exec:6» :: «exec:5» => (let typeIR_cast_step : typeIR := «exec:6»; (let «tail:2» : (_root_.List typeIR) := «exec:5»; (.bind (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«$chain_casts_recordTypeIR_default:case_1:iter:5» «tail:0» «tail:1» «tail:2»⟩) (fun («exec:7» : (_root_.List fieldTypeIR)) => (let «tail:3» : (_root_.List fieldTypeIR) := «exec:7»; (.pure (((((fieldTypeIR.«% % % ';'» annotationList_a typeIR_cast_step id_a) : fieldTypeIR) :: «tail:3») : (_root_.List fieldTypeIR))))))))) | [] => .unmatch))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$chain_casts_recordTypeIR_default:case_1:iter:5_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$chain_casts_recordTypeIR_default:case_1:iter:5:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$chain_casts_recordTypeIR_default:case_1:iter:5:clause:1»  input0 input1 input2)]


noncomputable def «$chain_casts_recordTypeIR_default:case_1:iter:4:clause:0» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List (_root_.List typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «annotationList_a*» : (_root_.List annotationList) := input0; (let «id_a*» : (_root_.List id) := input1; (match input2 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)))


noncomputable def «$chain_casts_recordTypeIR_default:case_1:iter:4:clause:1» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List (_root_.List typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «annotationList_a*» : (_root_.List annotationList) := input0; (let «id_a*» : (_root_.List id) := input1; (match input2 with | «exec:2» :: «exec:1» => (let «typeIR_cast_step*» : (_root_.List typeIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.List typeIR)) := «exec:1»; (.bind (.call ⟨(_root_.List fieldTypeIR), SpecTecCall.«$chain_casts_recordTypeIR_default:case_1:iter:5» «annotationList_a*» «id_a*» «typeIR_cast_step*»⟩) (fun («exec:3» : (_root_.List fieldTypeIR)) => (let «eval:6» : (_root_.List fieldTypeIR) := «exec:3»; (let typeIR_cast_agg : typeIR := ((typeIR.«RECORD `{ % ',' '...' `}» «eval:6») : typeIR); (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$chain_casts_recordTypeIR_default:case_1:iter:4» «annotationList_a*» «id_a*» «tail:0»⟩) (fun («exec:4» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:4»; (.pure (((typeIR_cast_agg :: «tail:1») : (_root_.List typeIR))))))))))))) | [] => .unmatch)))


noncomputable def «$chain_casts_recordTypeIR_default:case_1:iter:4_clauses» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List (_root_.List typeIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$chain_casts_recordTypeIR_default:case_1:iter:4:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$chain_casts_recordTypeIR_default:case_1:iter:4:clause:1»  input0 input1 input2)]


noncomputable def «$chain_casts_recordTypeIR_default:clause:0» (input0 : (_root_.List fieldTypeIR)) (input1 : (_root_.List (_root_.List typeIR))) (input2 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «eval:1» : (_root_.List fieldTypeIR) := input0; (let «typeIR_cast_elem**» : (_root_.List (_root_.List typeIR)) := input1; (let typeIR_b : typeIR := input2; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$chain_casts_recordTypeIR_default:case_1:pattern-iter:0» «eval:1»⟩) (fun («exec:1» : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))) => (let «annotationList_a*» : (_root_.List annotationList) := («exec:1»).1; (let «id_a*» : (_root_.List id) := ((«exec:1»).2).1; (let «typeIR_a*» : (_root_.List typeIR) := ((«exec:1»).2).2; (.bind (.call ⟨(_root_.List (_root_.List typeIR)), SpecTecCall.«$chain_casts» «typeIR_a*» «typeIR_cast_elem**»⟩) (fun («exec:2» : (_root_.List (_root_.List typeIR))) => (let «eval:2» : (_root_.List (_root_.List typeIR)) := «exec:2»; (let «typeIR_cast_step**» : (_root_.List (_root_.List typeIR)) := «eval:2»; (.bind (.call ⟨_root_.Unit, SpecTecCall.«$chain_casts_recordTypeIR_default:case_1:iter:3» «annotationList_a*» «id_a*» «typeIR_cast_step**»⟩) (fun («exec:3» : _root_.Unit) => (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$chain_casts_recordTypeIR_default:case_1:iter:4» «annotationList_a*» «id_a*» «typeIR_cast_step**»⟩) (fun («exec:4» : (_root_.List typeIR)) => (let «typeIR_cast_agg*» : (_root_.List typeIR) := «exec:4»; (.pure (((«typeIR_cast_agg*» ++ ([typeIR_b] : (_root_.List typeIR))) : (_root_.List typeIR)))))))))))))))))))))


noncomputable def «$chain_casts_recordTypeIR_default_clauses» (input0 : (_root_.List fieldTypeIR)) (input1 : (_root_.List (_root_.List typeIR))) (input2 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$chain_casts_recordTypeIR_default:clause:0»  input0 input1 input2)]


noncomputable def «$apply_cast:clause:0» (input0 : SpecTec.typedExpressionIR) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typedExpressionIR : SpecTec.typedExpressionIR := input0; (let «typeIR*» : (_root_.List typeIR) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeIR*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((typedExpressionIR : SpecTec.typedExpressionIR)))))))

end SpecTec
