import SpecTecDecl0272

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$free_typeIR:case_9:iter:6_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_9:iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_9:iter:6:clause:1»  input0)]


noncomputable def «$free_typeIR:case_10:iter:3:clause:0» (input0 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_typeIR:case_10:iter:3:clause:1» (input0 : (_root_.List SpecTec.typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeArgumentIR⟩) (fun («exec:3» : bound) => (let «eval:4» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_10:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:4» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_10:iter:3_clauses» (input0 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_10:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_10:iter:3:clause:1»  input0)]


noncomputable def «$free_typeIR:case_10:iter:6:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_typeIR:case_10:iter:6:clause:1» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_field : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeIR_field⟩) (fun («exec:3» : bound) => (let «eval:7» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_10:iter:6» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:7» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_10:iter:6_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_10:iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_10:iter:6:clause:1»  input0)]


noncomputable def «$free_typeIR:case_11:iter:3:clause:0» (input0 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_typeIR:case_11:iter:3:clause:1» (input0 : (_root_.List SpecTec.typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeArgumentIR⟩) (fun («exec:3» : bound) => (let «eval:4» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_11:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:4» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_11:iter:3_clauses» (input0 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_11:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_11:iter:3:clause:1»  input0)]


noncomputable def «$free_typeIR:case_11:iter:6:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_typeIR:case_11:iter:6:clause:1» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_field : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeIR_field⟩) (fun («exec:3» : bound) => (let «eval:7» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_11:iter:6» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:7» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_11:iter:6_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_11:iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_11:iter:6:clause:1»  input0)]


noncomputable def «$free_typeIR:case_14:iter:3:clause:0» (input0 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_typeIR:case_14:iter:3:clause:1» (input0 : (_root_.List SpecTec.typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeArgumentIR⟩) (fun («exec:3» : bound) => (let «eval:4» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_14:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:4» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_14:iter:3_clauses» (input0 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_14:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_14:iter:3:clause:1»  input0)]


noncomputable def «$free_typeIR:case_14:iter:6:clause:0» (input0 : (_root_.List externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_typeIR:case_14:iter:6:clause:1» (input0 : (_root_.List SpecTec.externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.externMethodTypeDefIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_callableTypeDefIR» («cast:externMethodTypeDefIR:callableTypeDefIR» externMethodTypeDefIR)⟩) (fun («exec:3» : bound) => (let «eval:7» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_14:iter:6» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:7» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_14:iter:6_clauses» (input0 : (_root_.List externMethodTypeDefIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_14:iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_14:iter:6:clause:1»  input0)]


noncomputable def «$free_typeIR:case_15:iter:1:clause:0» (input0 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_typeIR:case_15:iter:1:clause:1» (input0 : (_root_.List SpecTec.typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeArgumentIR⟩) (fun («exec:3» : bound) => (let «eval:2» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_15:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:2» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_15:iter:1_clauses» (input0 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_15:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_15:iter:1:clause:1»  input0)]


noncomputable def «$free_typeIR:case_15:iter:4:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_typeIR:case_15:iter:4:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_parameterIR» parameterIR⟩) (fun («exec:3» : bound) => (let «eval:5» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_15:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:5» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_15:iter:4_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_15:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_15:iter:4:clause:1»  input0)]


noncomputable def «$free_typeIR:case_16:iter:1:clause:0» (input0 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_typeIR:case_16:iter:1:clause:1» (input0 : (_root_.List SpecTec.typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeArgumentIR⟩) (fun («exec:3» : bound) => (let «eval:2» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_16:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:2» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_16:iter:1_clauses» (input0 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_16:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_16:iter:1:clause:1»  input0)]


noncomputable def «$free_typeIR:case_16:iter:4:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_typeIR:case_16:iter:4:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_parameterIR» parameterIR⟩) (fun («exec:3» : bound) => (let «eval:5» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_16:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:5» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_16:iter:4_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_16:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_16:iter:4:clause:1»  input0)]


noncomputable def «$free_typeIR:case_17:iter:1:clause:0» (input0 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)

end SpecTec
