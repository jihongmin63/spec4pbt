import SpecTecDecl0236

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$assignop_as_binop:clause:7» (input0 : SpecTec.assignop) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let assignop : SpecTec.assignop := input0; (.bind (.guard (((«exec:match:assignop:'<<='» assignop) = true))) (fun (_ : Unit) => (.pure (((_root_.Option.some ((binop.«'<<'») : binop)) : (_root_.Option binop)))))))


noncomputable def «$assignop_as_binop:clause:8» (input0 : SpecTec.assignop) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let assignop : SpecTec.assignop := input0; (.bind (.guard (((«exec:match:assignop:'>>='» assignop) = true))) (fun (_ : Unit) => (.pure (((_root_.Option.some ((binop.«'>>'») : binop)) : (_root_.Option binop)))))))


noncomputable def «$assignop_as_binop:clause:9» (input0 : SpecTec.assignop) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let assignop : SpecTec.assignop := input0; (.bind (.guard (((«exec:match:assignop:'&='» assignop) = true))) (fun (_ : Unit) => (.pure (((_root_.Option.some ((binop.«'&'») : binop)) : (_root_.Option binop)))))))


noncomputable def «$assignop_as_binop:clause:10» (input0 : SpecTec.assignop) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let assignop : SpecTec.assignop := input0; (.bind (.guard (((«exec:match:assignop:'^='» assignop) = true))) (fun (_ : Unit) => (.pure (((_root_.Option.some ((binop.«'^'») : binop)) : (_root_.Option binop)))))))


noncomputable def «$assignop_as_binop:clause:11» (input0 : SpecTec.assignop) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let assignop : SpecTec.assignop := input0; (.bind (.guard (((«exec:match:assignop:'|='» assignop) = true))) (fun (_ : Unit) => (.pure (((_root_.Option.some ((binop.«'|'») : binop)) : (_root_.Option binop)))))))


noncomputable def «$assignop_as_binop:clause:12» (input0 : SpecTec.assignop) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let assignop : SpecTec.assignop := input0; (.pure ((((_root_.Option.none) : (_root_.Option binop)) : (_root_.Option binop)))))


noncomputable def «$assignop_as_binop_clauses» (input0 : assignop) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$assignop_as_binop:clause:0»  input0), fun (_ : _root_.Unit) => («$assignop_as_binop:clause:1»  input0), fun (_ : _root_.Unit) => («$assignop_as_binop:clause:2»  input0), fun (_ : _root_.Unit) => («$assignop_as_binop:clause:3»  input0), fun (_ : _root_.Unit) => («$assignop_as_binop:clause:4»  input0), fun (_ : _root_.Unit) => («$assignop_as_binop:clause:5»  input0), fun (_ : _root_.Unit) => («$assignop_as_binop:clause:6»  input0), fun (_ : _root_.Unit) => («$assignop_as_binop:clause:7»  input0), fun (_ : _root_.Unit) => («$assignop_as_binop:clause:8»  input0), fun (_ : _root_.Unit) => («$assignop_as_binop:clause:9»  input0), fun (_ : _root_.Unit) => («$assignop_as_binop:clause:10»  input0), fun (_ : _root_.Unit) => («$assignop_as_binop:clause:11»  input0), fun (_ : _root_.Unit) => («$assignop_as_binop:clause:12»  input0)]


noncomputable def «$flatten_blockElementStatementList:clause:0» (input0 : SpecTec.blockElementStatementList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let blockElementStatementList : SpecTec.blockElementStatementList := input0; (.bind (.guard (((«exec:match:blockElementStatementList:_EMPTY» blockElementStatementList) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List blockElementStatement)) : (_root_.List blockElementStatement)))))))


noncomputable def «$flatten_blockElementStatementList:clause:1» (input0 : SpecTec.blockElementStatementList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let blockElementStatementList' : SpecTec.blockElementStatementList := input0; (.bind (.guard (((«exec:match:blockElementStatementList:% %» blockElementStatementList') = true))) (fun (_ : Unit) => (match blockElementStatementList' with | .«% %» «exec:1» «exec:2» => (let blockElementStatementList : SpecTec.blockElementStatementList := «exec:1»; (let blockElementStatement : SpecTec.blockElementStatement := «exec:2»; (.bind (.call ⟨(_root_.List SpecTec.blockElementStatement), SpecTecCall.«$flatten_blockElementStatementList» blockElementStatementList⟩) (fun («exec:3» : (_root_.List SpecTec.blockElementStatement)) => (let «eval:0» : (_root_.List SpecTec.blockElementStatement) := «exec:3»; (.pure (((«eval:0» ++ ([blockElementStatement] : (_root_.List SpecTec.blockElementStatement))) : (_root_.List SpecTec.blockElementStatement))))))))) | _ => .unmatch))))


noncomputable def «$flatten_blockElementStatementList_clauses» (input0 : blockElementStatementList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_blockElementStatementList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_blockElementStatementList:clause:1»  input0)]


noncomputable def «Cast_expl_neq:listTypeIR:iter:3:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:listTypeIR:iter:3:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (.bind (.guard (((«exec:match:castResult:OK» castResult) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:listTypeIR:iter:3» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:listTypeIR:iter:3_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:listTypeIR:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:listTypeIR:iter:3:clause:1»  input0)]


noncomputable def «Cast_expl_neq:tupleTypeIR:iter:3:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:tupleTypeIR:iter:3:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (.bind (.guard (((«exec:match:castResult:OK» castResult) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:tupleTypeIR:iter:3» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:tupleTypeIR:iter:3_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:tupleTypeIR:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:tupleTypeIR:iter:3:clause:1»  input0)]


noncomputable def «Cast_expl_neq:arrayTypeIR:iter:3:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:arrayTypeIR:iter:3:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (.bind (.guard (((«exec:match:castResult:OK» castResult) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:arrayTypeIR:iter:3» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:arrayTypeIR:iter:3_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:arrayTypeIR:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:arrayTypeIR:iter:3:clause:1»  input0)]


noncomputable def «Cast_expl_neq:headerStackTypeIR:iter:3:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:headerStackTypeIR:iter:3:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (.bind (.guard (((«exec:match:castResult:OK» castResult) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:headerStackTypeIR:iter:3» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:headerStackTypeIR:iter:3_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:headerStackTypeIR:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:headerStackTypeIR:iter:3:clause:1»  input0)]


noncomputable def «Cast_expl_neq:structTypeIR:iter:5:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:structTypeIR:iter:5:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (.bind (.guard (((«exec:match:castResult:OK» castResult) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:structTypeIR:iter:5» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:structTypeIR:iter:5_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:structTypeIR:iter:5:clause:1»  input0)]


noncomputable def «Cast_expl_neq:headerTypeIR_2:iter:5:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_2:iter:5:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (.bind (.guard (((«exec:match:castResult:OK» castResult) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:headerTypeIR_2:iter:5» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:headerTypeIR_2:iter:5_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_2:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:headerTypeIR_2:iter:5:clause:1»  input0)]


noncomputable def «Cast_expl_neq:tupleTypeIR_2:iter:4:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_expl_neq:tupleTypeIR_2:iter:4:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (.bind (.guard (((«exec:match:castResult:OK» castResult) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_expl_neq:tupleTypeIR_2:iter:4» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_expl_neq:tupleTypeIR_2:iter:4_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_expl_neq:tupleTypeIR_2:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_expl_neq:tupleTypeIR_2:iter:4:clause:1»  input0)]


noncomputable def «Cast_expl_neq:arrayTypeIR_2:iter:3:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)

end SpecTec
