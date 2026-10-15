import SpecTecDecl0293

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Call_ok:definedFunctionTypeIR:iter:3_clauses» (input0 : inference) (input1 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_ok:definedFunctionTypeIR:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Call_ok:definedFunctionTypeIR:iter:3:clause:1»  input0 input1)]


noncomputable def «Call_ok:definedFunctionTypeIR:iter:5:clause:0» (input0 : SpecTec.inference) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | [] => (.pure ((([] : (_root_.List parameterIR)) : (_root_.List parameterIR)))) | _ :: _ => .unmatch))


noncomputable def «Call_ok:definedFunctionTypeIR:iter:5:clause:1» (input0 : SpecTec.inference) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR_aligned : parameterIR := «exec:2»; (let «tail:0» : (_root_.List parameterIR) := «exec:1»; (.bind (.call ⟨parameterIR, SpecTecCall.«$subst_parameterIR» inference parameterIR_aligned⟩) (fun («exec:3» : parameterIR) => (let «eval:6» : parameterIR := «exec:3»; (let parameterIR_aligned_inferred : parameterIR := «eval:6»; (.bind (.call ⟨(_root_.List parameterIR), SpecTecCall.«Call_ok:definedFunctionTypeIR:iter:5» inference «tail:0»⟩) (fun («exec:4» : (_root_.List parameterIR)) => (let «tail:1» : (_root_.List parameterIR) := «exec:4»; (.pure (((parameterIR_aligned_inferred :: «tail:1») : (_root_.List parameterIR))))))))))))) | [] => .unmatch))


noncomputable def «Call_ok:definedFunctionTypeIR:iter:5_clauses» (input0 : inference) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_ok:definedFunctionTypeIR:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Call_ok:definedFunctionTypeIR:iter:5:clause:1»  input0 input1)]


noncomputable def «Call_ok:externFunctionTypeIR:iter:3:clause:0» (input0 : SpecTec.inference) (input1 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeArgumentIR)) : (_root_.List typeArgumentIR)))) | _ :: _ => .unmatch))


noncomputable def «Call_ok:externFunctionTypeIR:iter:3:clause:1» (input0 : SpecTec.inference) (input1 : (_root_.List SpecTec.typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (.bind (.call ⟨typeIR, SpecTecCall.«$subst_typeIR» inference typeArgumentIR⟩) (fun («exec:3» : typeIR) => (let «eval:4» : typeIR := «exec:3»; (let typeArgumentIR_inferred : SpecTec.typeArgumentIR := «eval:4»; (.bind (.call ⟨(_root_.List SpecTec.typeArgumentIR), SpecTecCall.«Call_ok:externFunctionTypeIR:iter:3» inference «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.typeArgumentIR)) => (let «tail:1» : (_root_.List SpecTec.typeArgumentIR) := «exec:4»; (.pure (((typeArgumentIR_inferred :: «tail:1») : (_root_.List SpecTec.typeArgumentIR))))))))))))) | [] => .unmatch))


noncomputable def «Call_ok:externFunctionTypeIR:iter:3_clauses» (input0 : inference) (input1 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_ok:externFunctionTypeIR:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Call_ok:externFunctionTypeIR:iter:3:clause:1»  input0 input1)]


noncomputable def «Call_ok:externFunctionTypeIR:iter:5:clause:0» (input0 : SpecTec.inference) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | [] => (.pure ((([] : (_root_.List parameterIR)) : (_root_.List parameterIR)))) | _ :: _ => .unmatch))


noncomputable def «Call_ok:externFunctionTypeIR:iter:5:clause:1» (input0 : SpecTec.inference) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR_aligned : parameterIR := «exec:2»; (let «tail:0» : (_root_.List parameterIR) := «exec:1»; (.bind (.call ⟨parameterIR, SpecTecCall.«$subst_parameterIR» inference parameterIR_aligned⟩) (fun («exec:3» : parameterIR) => (let «eval:6» : parameterIR := «exec:3»; (let parameterIR_aligned_inferred : parameterIR := «eval:6»; (.bind (.call ⟨(_root_.List parameterIR), SpecTecCall.«Call_ok:externFunctionTypeIR:iter:5» inference «tail:0»⟩) (fun («exec:4» : (_root_.List parameterIR)) => (let «tail:1» : (_root_.List parameterIR) := «exec:4»; (.pure (((parameterIR_aligned_inferred :: «tail:1») : (_root_.List parameterIR))))))))))))) | [] => .unmatch))


noncomputable def «Call_ok:externFunctionTypeIR:iter:5_clauses» (input0 : inference) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_ok:externFunctionTypeIR:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Call_ok:externFunctionTypeIR:iter:5:clause:1»  input0 input1)]


noncomputable def «Call_ok:non-abstract:iter:3:clause:0» (input0 : SpecTec.inference) (input1 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeArgumentIR)) : (_root_.List typeArgumentIR)))) | _ :: _ => .unmatch))


noncomputable def «Call_ok:non-abstract:iter:3:clause:1» (input0 : SpecTec.inference) (input1 : (_root_.List SpecTec.typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (.bind (.call ⟨typeIR, SpecTecCall.«$subst_typeIR» inference typeArgumentIR⟩) (fun («exec:3» : typeIR) => (let «eval:4» : typeIR := «exec:3»; (let typeArgumentIR_inferred : SpecTec.typeArgumentIR := «eval:4»; (.bind (.call ⟨(_root_.List SpecTec.typeArgumentIR), SpecTecCall.«Call_ok:non-abstract:iter:3» inference «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.typeArgumentIR)) => (let «tail:1» : (_root_.List SpecTec.typeArgumentIR) := «exec:4»; (.pure (((typeArgumentIR_inferred :: «tail:1») : (_root_.List SpecTec.typeArgumentIR))))))))))))) | [] => .unmatch))


noncomputable def «Call_ok:non-abstract:iter:3_clauses» (input0 : inference) (input1 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_ok:non-abstract:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Call_ok:non-abstract:iter:3:clause:1»  input0 input1)]


noncomputable def «Call_ok:non-abstract:iter:5:clause:0» (input0 : SpecTec.inference) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | [] => (.pure ((([] : (_root_.List parameterIR)) : (_root_.List parameterIR)))) | _ :: _ => .unmatch))


noncomputable def «Call_ok:non-abstract:iter:5:clause:1» (input0 : SpecTec.inference) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR_aligned : parameterIR := «exec:2»; (let «tail:0» : (_root_.List parameterIR) := «exec:1»; (.bind (.call ⟨parameterIR, SpecTecCall.«$subst_parameterIR» inference parameterIR_aligned⟩) (fun («exec:3» : parameterIR) => (let «eval:6» : parameterIR := «exec:3»; (let parameterIR_aligned_inferred : parameterIR := «eval:6»; (.bind (.call ⟨(_root_.List parameterIR), SpecTecCall.«Call_ok:non-abstract:iter:5» inference «tail:0»⟩) (fun («exec:4» : (_root_.List parameterIR)) => (let «tail:1» : (_root_.List parameterIR) := «exec:4»; (.pure (((parameterIR_aligned_inferred :: «tail:1») : (_root_.List parameterIR))))))))))))) | [] => .unmatch))


noncomputable def «Call_ok:non-abstract:iter:5_clauses» (input0 : inference) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_ok:non-abstract:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Call_ok:non-abstract:iter:5:clause:1»  input0 input1)]


noncomputable def «Call_ok:abstract:iter:3:clause:0» (input0 : SpecTec.inference) (input1 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeArgumentIR)) : (_root_.List typeArgumentIR)))) | _ :: _ => .unmatch))


noncomputable def «Call_ok:abstract:iter:3:clause:1» (input0 : SpecTec.inference) (input1 : (_root_.List SpecTec.typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (.bind (.call ⟨typeIR, SpecTecCall.«$subst_typeIR» inference typeArgumentIR⟩) (fun («exec:3» : typeIR) => (let «eval:4» : typeIR := «exec:3»; (let typeArgumentIR_inferred : SpecTec.typeArgumentIR := «eval:4»; (.bind (.call ⟨(_root_.List SpecTec.typeArgumentIR), SpecTecCall.«Call_ok:abstract:iter:3» inference «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.typeArgumentIR)) => (let «tail:1» : (_root_.List SpecTec.typeArgumentIR) := «exec:4»; (.pure (((typeArgumentIR_inferred :: «tail:1») : (_root_.List SpecTec.typeArgumentIR))))))))))))) | [] => .unmatch))


noncomputable def «Call_ok:abstract:iter:3_clauses» (input0 : inference) (input1 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_ok:abstract:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Call_ok:abstract:iter:3:clause:1»  input0 input1)]


noncomputable def «Call_ok:abstract:iter:5:clause:0» (input0 : SpecTec.inference) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | [] => (.pure ((([] : (_root_.List parameterIR)) : (_root_.List parameterIR)))) | _ :: _ => .unmatch))


noncomputable def «Call_ok:abstract:iter:5:clause:1» (input0 : SpecTec.inference) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR_aligned : parameterIR := «exec:2»; (let «tail:0» : (_root_.List parameterIR) := «exec:1»; (.bind (.call ⟨parameterIR, SpecTecCall.«$subst_parameterIR» inference parameterIR_aligned⟩) (fun («exec:3» : parameterIR) => (let «eval:6» : parameterIR := «exec:3»; (let parameterIR_aligned_inferred : parameterIR := «eval:6»; (.bind (.call ⟨(_root_.List parameterIR), SpecTecCall.«Call_ok:abstract:iter:5» inference «tail:0»⟩) (fun («exec:4» : (_root_.List parameterIR)) => (let «tail:1» : (_root_.List parameterIR) := «exec:4»; (.pure (((parameterIR_aligned_inferred :: «tail:1») : (_root_.List parameterIR))))))))))))) | [] => .unmatch))


noncomputable def «Call_ok:abstract:iter:5_clauses» (input0 : inference) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_ok:abstract:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Call_ok:abstract:iter:5:clause:1»  input0 input1)]


noncomputable def «Inst_ok:package:iter:2:clause:0» (input0 : SpecTec.inference) (input1 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeArgumentIR)) : (_root_.List typeArgumentIR)))) | _ :: _ => .unmatch))


noncomputable def «Inst_ok:package:iter:2:clause:1» (input0 : SpecTec.inference) (input1 : (_root_.List SpecTec.typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (.bind (.call ⟨typeIR, SpecTecCall.«$subst_typeIR» inference typeArgumentIR⟩) (fun («exec:3» : typeIR) => (let «eval:3» : typeIR := «exec:3»; (let typeArgumentIR_inferred : SpecTec.typeArgumentIR := «eval:3»; (.bind (.call ⟨(_root_.List SpecTec.typeArgumentIR), SpecTecCall.«Inst_ok:package:iter:2» inference «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.typeArgumentIR)) => (let «tail:1» : (_root_.List SpecTec.typeArgumentIR) := «exec:4»; (.pure (((typeArgumentIR_inferred :: «tail:1») : (_root_.List SpecTec.typeArgumentIR))))))))))))) | [] => .unmatch))


noncomputable def «Inst_ok:package:iter:2_clauses» (input0 : inference) (input1 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Inst_ok:package:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Inst_ok:package:iter:2:clause:1»  input0 input1)]


noncomputable def «Inst_ok:package:iter:4:clause:0» (input0 : SpecTec.inference) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | [] => (.pure ((([] : (_root_.List parameterIR)) : (_root_.List parameterIR)))) | _ :: _ => .unmatch))


noncomputable def «Inst_ok:package:iter:4:clause:1» (input0 : SpecTec.inference) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR_aligned : parameterIR := «exec:2»; (let «tail:0» : (_root_.List parameterIR) := «exec:1»; (.bind (.call ⟨parameterIR, SpecTecCall.«$subst_parameterIR» inference parameterIR_aligned⟩) (fun («exec:3» : parameterIR) => (let «eval:5» : parameterIR := «exec:3»; (let parameterIR_aligned_inferred : parameterIR := «eval:5»; (.bind (.call ⟨(_root_.List parameterIR), SpecTecCall.«Inst_ok:package:iter:4» inference «tail:0»⟩) (fun («exec:4» : (_root_.List parameterIR)) => (let «tail:1» : (_root_.List parameterIR) := «exec:4»; (.pure (((parameterIR_aligned_inferred :: «tail:1») : (_root_.List parameterIR))))))))))))) | [] => .unmatch))


noncomputable def «Inst_ok:package:iter:4_clauses» (input0 : inference) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Inst_ok:package:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Inst_ok:package:iter:4:clause:1»  input0 input1)]


noncomputable def «Inst_ok:non-package:iter:2:clause:0» (input0 : SpecTec.inference) (input1 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | [] => (.pure ((([] : (_root_.List typeArgumentIR)) : (_root_.List typeArgumentIR)))) | _ :: _ => .unmatch))


noncomputable def «Inst_ok:non-package:iter:2:clause:1» (input0 : SpecTec.inference) (input1 : (_root_.List SpecTec.typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (.bind (.call ⟨typeIR, SpecTecCall.«$subst_typeIR» inference typeArgumentIR⟩) (fun («exec:3» : typeIR) => (let «eval:3» : typeIR := «exec:3»; (let typeArgumentIR_inferred : SpecTec.typeArgumentIR := «eval:3»; (.bind (.call ⟨(_root_.List SpecTec.typeArgumentIR), SpecTecCall.«Inst_ok:non-package:iter:2» inference «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.typeArgumentIR)) => (let «tail:1» : (_root_.List SpecTec.typeArgumentIR) := «exec:4»; (.pure (((typeArgumentIR_inferred :: «tail:1») : (_root_.List SpecTec.typeArgumentIR))))))))))))) | [] => .unmatch))


noncomputable def «Inst_ok:non-package:iter:2_clauses» (input0 : inference) (input1 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Inst_ok:non-package:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Inst_ok:non-package:iter:2:clause:1»  input0 input1)]


noncomputable def «Inst_ok:non-package:iter:4:clause:0» (input0 : SpecTec.inference) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let inference : SpecTec.inference := input0; (match input1 with | [] => (.pure ((([] : (_root_.List parameterIR)) : (_root_.List parameterIR)))) | _ :: _ => .unmatch))

end SpecTec
