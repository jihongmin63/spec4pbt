import SpecTecDecl0277

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$subst_typeIR':case_16:iter:1:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (.bind (.call ⟨typeIR, SpecTecCall.«$subst_typeIR'» theta typeArgumentIR⟩) (fun («exec:3» : typeIR) => (let «eval:2» : typeIR := «exec:3»; (let typeArgumentIR_subst : SpecTec.typeArgumentIR := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.typeArgumentIR), SpecTecCall.«$subst_typeIR':case_16:iter:1» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.typeArgumentIR)) => (let «tail:1» : (_root_.List SpecTec.typeArgumentIR) := «exec:4»; (.pure (((typeArgumentIR_subst :: «tail:1») : (_root_.List SpecTec.typeArgumentIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_typeIR':case_16:iter:1_clauses» (input0 : theta) (input1 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_16:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':case_16:iter:1:clause:1»  input0 input1)]


noncomputable def «$subst_typeIR':case_16:iter:3:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List parameterIR)) : (_root_.List parameterIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_typeIR':case_16:iter:3:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨SpecTec.parameterIR, SpecTecCall.«$subst_parameterIR'» theta parameterIR⟩) (fun («exec:3» : SpecTec.parameterIR) => (let «eval:4» : SpecTec.parameterIR := «exec:3»; (let parameterIR_subst : SpecTec.parameterIR := «eval:4»; (.bind (.call ⟨(_root_.List SpecTec.parameterIR), SpecTecCall.«$subst_typeIR':case_16:iter:3» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.parameterIR)) => (let «tail:1» : (_root_.List SpecTec.parameterIR) := «exec:4»; (.pure (((parameterIR_subst :: «tail:1») : (_root_.List SpecTec.parameterIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_typeIR':case_16:iter:3_clauses» (input0 : theta) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_16:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':case_16:iter:3:clause:1»  input0 input1)]


noncomputable def «$subst_typeIR':case_17:iter:1:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeArgumentIR)) : (_root_.List typeArgumentIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_typeIR':case_17:iter:1:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (.bind (.call ⟨typeIR, SpecTecCall.«$subst_typeIR'» theta typeArgumentIR⟩) (fun («exec:3» : typeIR) => (let «eval:2» : typeIR := «exec:3»; (let typeArgumentIR_subst : SpecTec.typeArgumentIR := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.typeArgumentIR), SpecTecCall.«$subst_typeIR':case_17:iter:1» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.typeArgumentIR)) => (let «tail:1» : (_root_.List SpecTec.typeArgumentIR) := «exec:4»; (.pure (((typeArgumentIR_subst :: «tail:1») : (_root_.List SpecTec.typeArgumentIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_typeIR':case_17:iter:1_clauses» (input0 : theta) (input1 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_17:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':case_17:iter:1:clause:1»  input0 input1)]


noncomputable def «$subst_typeIR':case_17:iter:3:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List parameterIR)) : (_root_.List parameterIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_typeIR':case_17:iter:3:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨SpecTec.parameterIR, SpecTecCall.«$subst_parameterIR'» theta parameterIR⟩) (fun («exec:3» : SpecTec.parameterIR) => (let «eval:4» : SpecTec.parameterIR := «exec:3»; (let parameterIR_subst : SpecTec.parameterIR := «eval:4»; (.bind (.call ⟨(_root_.List SpecTec.parameterIR), SpecTecCall.«$subst_typeIR':case_17:iter:3» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.parameterIR)) => (let «tail:1» : (_root_.List SpecTec.parameterIR) := «exec:4»; (.pure (((parameterIR_subst :: «tail:1») : (_root_.List SpecTec.parameterIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_typeIR':case_17:iter:3_clauses» (input0 : theta) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_17:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':case_17:iter:3:clause:1»  input0 input1)]


noncomputable def «$subst_typeIR':case_18:iter:1:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeArgumentIR)) : (_root_.List typeArgumentIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_typeIR':case_18:iter:1:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (.bind (.call ⟨typeIR, SpecTecCall.«$subst_typeIR'» theta typeArgumentIR⟩) (fun («exec:3» : typeIR) => (let «eval:2» : typeIR := «exec:3»; (let typeArgumentIR_subst : SpecTec.typeArgumentIR := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.typeArgumentIR), SpecTecCall.«$subst_typeIR':case_18:iter:1» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.typeArgumentIR)) => (let «tail:1» : (_root_.List SpecTec.typeArgumentIR) := «exec:4»; (.pure (((typeArgumentIR_subst :: «tail:1») : (_root_.List SpecTec.typeArgumentIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_typeIR':case_18:iter:1_clauses» (input0 : theta) (input1 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_18:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':case_18:iter:1:clause:1»  input0 input1)]


noncomputable def «$subst_typeIR':case_18:iter:3:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_typeIR':case_18:iter:3:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$subst_typeIR'» theta typeIR⟩) (fun («exec:3» : SpecTec.typeIR) => (let «eval:4» : SpecTec.typeIR := «exec:3»; (let typeIR_subst : SpecTec.typeIR := «eval:4»; (.bind (.call ⟨(_root_.List SpecTec.typeIR), SpecTecCall.«$subst_typeIR':case_18:iter:3» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.typeIR)) => (let «tail:1» : (_root_.List SpecTec.typeIR) := «exec:4»; (.pure (((typeIR_subst :: «tail:1») : (_root_.List SpecTec.typeIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_typeIR':case_18:iter:3_clauses» (input0 : theta) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_18:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':case_18:iter:3:clause:1»  input0 input1)]


noncomputable def «$subst_typeIR':case_22:iter:1:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_typeIR':case_22:iter:1:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$subst_typeIR'» theta typeIR⟩) (fun («exec:3» : SpecTec.typeIR) => (let «eval:2» : SpecTec.typeIR := «exec:3»; (let typeIR_subst : SpecTec.typeIR := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.typeIR), SpecTecCall.«$subst_typeIR':case_22:iter:1» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.typeIR)) => (let «tail:1» : (_root_.List SpecTec.typeIR) := «exec:4»; (.pure (((typeIR_subst :: «tail:1») : (_root_.List SpecTec.typeIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_typeIR':case_22:iter:1_clauses» (input0 : theta) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_22:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':case_22:iter:1:clause:1»  input0 input1)]


noncomputable def «$subst_typeIR':case_23:iter:1:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_typeIR':case_23:iter:1:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$subst_typeIR'» theta typeIR⟩) (fun («exec:3» : SpecTec.typeIR) => (let «eval:2» : SpecTec.typeIR := «exec:3»; (let typeIR_subst : SpecTec.typeIR := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.typeIR), SpecTecCall.«$subst_typeIR':case_23:iter:1» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.typeIR)) => (let «tail:1» : (_root_.List SpecTec.typeIR) := «exec:4»; (.pure (((typeIR_subst :: «tail:1») : (_root_.List SpecTec.typeIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_typeIR':case_23:iter:1_clauses» (input0 : theta) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_23:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':case_23:iter:1:clause:1»  input0 input1)]


noncomputable def «$subst_typeIR':case_24:iter:3:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_typeIR':case_24:iter:3:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeIR_field : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨typeIR, SpecTecCall.«$subst_typeIR'» theta typeIR_field⟩) (fun («exec:3» : typeIR) => (let «eval:4» : typeIR := «exec:3»; (let typeIR_field_subst : typeIR := «eval:4»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$subst_typeIR':case_24:iter:3» theta «tail:0»⟩) (fun («exec:4» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:4»; (.pure (((typeIR_field_subst :: «tail:1») : (_root_.List typeIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_typeIR':case_24:iter:3_clauses» (input0 : theta) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_24:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':case_24:iter:3:clause:1»  input0 input1)]


noncomputable def «$subst_typeIR':case_25:iter:3:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_typeIR':case_25:iter:3:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeIR_field : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨typeIR, SpecTecCall.«$subst_typeIR'» theta typeIR_field⟩) (fun («exec:3» : typeIR) => (let «eval:4» : typeIR := «exec:3»; (let typeIR_field_subst : typeIR := «eval:4»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$subst_typeIR':case_25:iter:3» theta «tail:0»⟩) (fun («exec:4» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:4»; (.pure (((typeIR_field_subst :: «tail:1») : (_root_.List typeIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_typeIR':case_25:iter:3_clauses» (input0 : theta) (input1 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_typeIR':case_25:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_typeIR':case_25:iter:3:clause:1»  input0 input1)]


noncomputable def «$subst_parameterIR:clause:0» (input0 : theta) (input1 : SpecTec.parameterIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «set<pair<typeId, typeIR>>» : (set (pair typeId typeIR)) := input0; (let parameterIR : SpecTec.parameterIR := input1; (.bind (.guard (((set.«`{ % `}» ([] : (_root_.List (pair typeId typeIR)))) : (set (pair typeId typeIR))) = «set<pair<typeId, typeIR>>»)) (fun (_ : Unit) => (.pure ((parameterIR : SpecTec.parameterIR)))))))


noncomputable def «$subst_parameterIR:clause:1» (input0 : SpecTec.theta) (input1 : SpecTec.parameterIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (let parameterIR : SpecTec.parameterIR := input1; (.bind (.call ⟨SpecTec.parameterIR, SpecTecCall.«$subst_parameterIR'» theta parameterIR⟩) (fun («exec:1» : SpecTec.parameterIR) => (let «eval:0» : SpecTec.parameterIR := «exec:1»; (.pure ((«eval:0» : SpecTec.parameterIR))))))))


noncomputable def «$subst_parameterIR_clauses» (input0 : theta) (input1 : parameterIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_parameterIR:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_parameterIR:clause:1»  input0 input1)]

end SpecTec
