import SpecTecDecl0150

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$free_typeIR:case_23:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR : SpecTec.typeIR := «exec:4»; (let _nameIR : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR))), SpecTecCall.«$free_typeIR:case_23:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List SpecTec.typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((_nameIR :: «pattern-tail:2»), (typeIR :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_23:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_23:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_23:pattern-iter:1:clause:1»  input0)]


noncomputable def «$free_typeIR:case_24:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$free_typeIR:case_24:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR : SpecTec.typeIR := «exec:4»; (let _nameIR : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR))), SpecTecCall.«$free_typeIR:case_24:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List SpecTec.typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((_nameIR :: «pattern-tail:2»), (typeIR :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_24:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_24:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_24:pattern-iter:1:clause:1»  input0)]


noncomputable def «$empty_theta:clause:0»  : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (.bind (.call ⟨(map typeId typeIR), SpecTecCall.«$empty_map» typeId typeIR⟩) (fun («exec:1» : (map typeId typeIR)) => (let «eval:0» : (map typeId typeIR) := «exec:1»; (.pure ((«eval:0» : theta))))))


noncomputable def «$empty_theta_clauses» : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$empty_theta:clause:0»  )]


noncomputable def «$capture_avoiding_:case_1:iter:0:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.Option typeIR))) : (_root_.List (_root_.Option typeIR))))) | _ :: _ => .unmatch))


noncomputable def «$capture_avoiding_:case_1:iter:0:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeId_free : typeId := «exec:2»; (let «tail:0» : (_root_.List typeId) := «exec:1»; (.bind (.call ⟨(_root_.Option typeIR), SpecTecCall.«$find_map» typeId typeIR theta typeId_free⟩) (fun («exec:3» : (_root_.Option typeIR)) => (let «eval:1» : (_root_.Option typeIR) := «exec:3»; (let typeIR? : (_root_.Option typeIR) := «eval:1»; (.bind (.call ⟨(_root_.List (_root_.Option typeIR)), SpecTecCall.«$capture_avoiding_:case_1:iter:0» theta «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.Option typeIR))) => (let «tail:1» : (_root_.List (_root_.Option typeIR)) := «exec:4»; (.pure (((typeIR? :: «tail:1») : (_root_.List (_root_.Option typeIR)))))))))))))) | [] => .unmatch))


noncomputable def «$capture_avoiding_:case_1:iter:0_clauses» (input0 : theta) (input1 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$capture_avoiding_:case_1:iter:0:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$capture_avoiding_:case_1:iter:0:clause:1»  input0 input1)]


noncomputable def «$capture_avoiding_:case_1:iter:2:clause:0» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «$capture_avoiding_:case_1:iter:2:clause:1» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR? : (_root_.Option typeIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option typeIR)) := «exec:1»; (.bind (.guard (((_root_.Option.isSome typeIR?) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$capture_avoiding_:case_1:iter:2» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «$capture_avoiding_:case_1:iter:2_clauses» (input0 : (_root_.List (_root_.Option typeIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$capture_avoiding_:case_1:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$capture_avoiding_:case_1:iter:2:clause:1»  input0)]


noncomputable def «$capture_avoiding_:case_1:iter:3:clause:0» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «$capture_avoiding_:case_1:iter:3:clause:1» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR? : (_root_.Option typeIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option typeIR)) := «exec:1»; (match typeIR? with | some «exec:3» => (let typeIR_free : typeIR := «exec:3»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$capture_avoiding_:case_1:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:4»; (.pure (((typeIR_free :: «tail:1») : (_root_.List typeIR)))))))) | none => .unmatch))) | [] => .unmatch)


noncomputable def «$capture_avoiding_:case_1:iter:3_clauses» (input0 : (_root_.List (_root_.Option typeIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$capture_avoiding_:case_1:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$capture_avoiding_:case_1:iter:3:clause:1»  input0)]


noncomputable def «$capture_avoiding_:case_1:iter:10:clause:0» (input0 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «$capture_avoiding_:case_1:iter:10:clause:1» (input0 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeParameterIR_fresh : typeParameterIR := «exec:2»; (let «tail:0» : (_root_.List typeParameterIR) := «exec:1»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$capture_avoiding_:case_1:iter:10» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((((typeIR._NAME typeParameterIR_fresh) : typeIR) :: «tail:1») : (_root_.List typeIR))))))))) | [] => .unmatch)


noncomputable def «$capture_avoiding_:case_1:iter:10_clauses» (input0 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$capture_avoiding_:case_1:iter:10:clause:0»  input0), fun (_ : _root_.Unit) => («$capture_avoiding_:case_1:iter:10:clause:1»  input0)]


noncomputable def «$capture_avoiding:case_1:iter:0:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.Option typeIR))) : (_root_.List (_root_.Option typeIR))))) | _ :: _ => .unmatch))


noncomputable def «$capture_avoiding:case_1:iter:0:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeId_free : typeId := «exec:2»; (let «tail:0» : (_root_.List typeId) := «exec:1»; (.bind (.call ⟨(_root_.Option typeIR), SpecTecCall.«$find_map» typeId typeIR theta typeId_free⟩) (fun («exec:3» : (_root_.Option typeIR)) => (let «eval:1» : (_root_.Option typeIR) := «exec:3»; (let typeIR? : (_root_.Option typeIR) := «eval:1»; (.bind (.call ⟨(_root_.List (_root_.Option typeIR)), SpecTecCall.«$capture_avoiding:case_1:iter:0» theta «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.Option typeIR))) => (let «tail:1» : (_root_.List (_root_.Option typeIR)) := «exec:4»; (.pure (((typeIR? :: «tail:1») : (_root_.List (_root_.Option typeIR)))))))))))))) | [] => .unmatch))


noncomputable def «$capture_avoiding:case_1:iter:0_clauses» (input0 : theta) (input1 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$capture_avoiding:case_1:iter:0:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$capture_avoiding:case_1:iter:0:clause:1»  input0 input1)]


noncomputable def «$capture_avoiding:case_1:iter:2:clause:0» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «$capture_avoiding:case_1:iter:2:clause:1» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR? : (_root_.Option typeIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option typeIR)) := «exec:1»; (.bind (.guard (((_root_.Option.isSome typeIR?) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$capture_avoiding:case_1:iter:2» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «$capture_avoiding:case_1:iter:2_clauses» (input0 : (_root_.List (_root_.Option typeIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$capture_avoiding:case_1:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$capture_avoiding:case_1:iter:2:clause:1»  input0)]


noncomputable def «$capture_avoiding:case_1:iter:3:clause:0» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «$capture_avoiding:case_1:iter:3:clause:1» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR? : (_root_.Option typeIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option typeIR)) := «exec:1»; (match typeIR? with | some «exec:3» => (let typeIR_free : typeIR := «exec:3»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$capture_avoiding:case_1:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:4»; (.pure (((typeIR_free :: «tail:1») : (_root_.List typeIR)))))))) | none => .unmatch))) | [] => .unmatch)


noncomputable def «$capture_avoiding:case_1:iter:3_clauses» (input0 : (_root_.List (_root_.Option typeIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$capture_avoiding:case_1:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$capture_avoiding:case_1:iter:3:clause:1»  input0)]


noncomputable def «$capture_avoiding:case_1:iter:10:clause:0» (input0 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «$capture_avoiding:case_1:iter:10:clause:1» (input0 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeParameterIR_expl_fresh : typeParameterIR := «exec:2»; (let «tail:0» : (_root_.List typeParameterIR) := «exec:1»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$capture_avoiding:case_1:iter:10» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((((typeIR._NAME typeParameterIR_expl_fresh) : typeIR) :: «tail:1») : (_root_.List typeIR))))))))) | [] => .unmatch)


noncomputable def «$capture_avoiding:case_1:iter:10_clauses» (input0 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$capture_avoiding:case_1:iter:10:clause:0»  input0), fun (_ : _root_.Unit) => («$capture_avoiding:case_1:iter:10:clause:1»  input0)]


noncomputable def «$capture_avoiding:case_1:iter:12:clause:0» (input0 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)

end SpecTec
