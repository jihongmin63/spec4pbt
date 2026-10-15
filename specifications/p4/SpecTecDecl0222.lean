import SpecTecDecl0221

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$find_object_unqualified_e:case_1:pattern-iter:0:clause:0» (input0 : (_root_.List (pair (_root_.List _root_.String) object))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List object)), ([] : (_root_.List objectId))) : ((_root_.List object) × (_root_.List objectId))))) | _ :: _ => .unmatch)


noncomputable def «$find_object_unqualified_e:case_1:pattern-iter:0:clause:1» (input0 : (_root_.List (pair (_root_.List _root_.String) SpecTec.object))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let objectId : SpecTec.objectId := «exec:3»; (let object : SpecTec.object := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair (_root_.List _root_.String) SpecTec.object)) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.object) × (_root_.List SpecTec.objectId)), SpecTecCall.«$find_object_unqualified_e:case_1:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.object) × (_root_.List SpecTec.objectId))) => (let «pattern-tail:1» : (_root_.List SpecTec.object) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.objectId) := («exec:5»).2; (.pure ((((object :: «pattern-tail:1»), (objectId :: «pattern-tail:2»)) : ((_root_.List SpecTec.object) × (_root_.List SpecTec.objectId))))))))))))) | [] => .unmatch)


noncomputable def «$find_object_unqualified_e:case_1:pattern-iter:0_clauses» (input0 : (_root_.List (pair (_root_.List _root_.String) object))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_object_unqualified_e:case_1:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$find_object_unqualified_e:case_1:pattern-iter:0:clause:1»  input0)]


noncomputable def «$find_object_unqualified_e:case_1:iter:2:clause:0» (input0 : SpecTec.id) (input1 : (_root_.List object)) (input2 : (_root_.List objectId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let id : SpecTec.id := input0; (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List (_root_.Option object))) : (_root_.List (_root_.Option object))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch))


noncomputable def «$find_object_unqualified_e:case_1:iter:2:clause:1» (input0 : SpecTec.id) (input1 : (_root_.List SpecTec.object)) (input2 : (_root_.List SpecTec.objectId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let id : SpecTec.id := input0; (match input1 with | «exec:2» :: «exec:1» => (let object : SpecTec.object := «exec:2»; (let «tail:0» : (_root_.List SpecTec.object) := «exec:1»; (match input2 with | «exec:4» :: «exec:3» => (let objectId : SpecTec.objectId := «exec:4»; (let «tail:1» : (_root_.List SpecTec.objectId) := «exec:3»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$objectId_ends_with» objectId id⟩) (fun («exec:5» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:5»; (.bind (.call ⟨(_root_.Option SpecTec.object), SpecTecCall.«$ite» (_root_.Option SpecTec.object) «eval:3» (_root_.Option.some object) ((_root_.Option.none) : (_root_.Option SpecTec.object))⟩) (fun («exec:6» : (_root_.Option SpecTec.object)) => (let «eval:4» : (_root_.Option SpecTec.object) := «exec:6»; (let object_id? : (_root_.Option SpecTec.object) := «eval:4»; (.bind (.call ⟨(_root_.List (_root_.Option SpecTec.object)), SpecTecCall.«$find_object_unqualified_e:case_1:iter:2» id «tail:0» «tail:1»⟩) (fun («exec:7» : (_root_.List (_root_.Option SpecTec.object))) => (let «tail:2» : (_root_.List (_root_.Option SpecTec.object)) := «exec:7»; (.pure (((object_id? :: «tail:2») : (_root_.List (_root_.Option SpecTec.object))))))))))))))))) | [] => .unmatch))) | [] => .unmatch))


noncomputable def «$find_object_unqualified_e:case_1:iter:2_clauses» (input0 : id) (input1 : (_root_.List object)) (input2 : (_root_.List objectId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_object_unqualified_e:case_1:iter:2:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$find_object_unqualified_e:case_1:iter:2:clause:1»  input0 input1 input2)]


noncomputable def «$find_object_unqualified_e:case_1:iter:5:clause:0» (input0 : (_root_.List (_root_.Option object))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$find_object_unqualified_e:case_1:iter:5:clause:1» (input0 : (_root_.List (_root_.Option object))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let object_id? : (_root_.Option object) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option object)) := «exec:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$find_object_unqualified_e:case_1:iter:5» «tail:0»⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:3»; (.pure ((((!(_root_.Option.isNone object_id?)) :: «tail:1») : (_root_.List _root_.Bool))))))))) | [] => .unmatch)


noncomputable def «$find_object_unqualified_e:case_1:iter:5_clauses» (input0 : (_root_.List (_root_.Option object))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_object_unqualified_e:case_1:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («$find_object_unqualified_e:case_1:iter:5:clause:1»  input0)]


noncomputable def «$find_object_unqualified_e:clause:0» (input0 : arch) (input1 : SpecTec.id) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let ARCH : arch := input0; (let id : SpecTec.id := input1; (match (arch.STORE ARCH) with | .«`{ % `}» «exec:1» => (let «eval:1» : (_root_.List (pair objectId object)) := «exec:1»; (.bind (.call ⟨((_root_.List object) × (_root_.List objectId)), SpecTecCall.«$find_object_unqualified_e:case_1:pattern-iter:0» «eval:1»⟩) (fun («exec:2» : ((_root_.List object) × (_root_.List objectId))) => (let «object*» : (_root_.List object) := («exec:2»).1; (let «objectId*» : (_root_.List objectId) := («exec:2»).2; (.bind (.call ⟨(_root_.List (_root_.Option object)), SpecTecCall.«$find_object_unqualified_e:case_1:iter:2» id «object*» «objectId*»⟩) (fun («exec:3» : (_root_.List (_root_.Option object))) => (let «object_id?*» : (_root_.List (_root_.Option object)) := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$find_object_unqualified_e:case_1:iter:5» «object_id?*»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «eval:6» : (_root_.List _root_.Bool) := «exec:4»; (.bind (.call ⟨(_root_.List (_root_.Option object)), SpecTecCall.«$filter_» (_root_.Option object) «object_id?*» «eval:6»⟩) (fun («exec:5» : (_root_.List (_root_.Option object))) => (let «eval:7» : (_root_.List (_root_.Option object)) := «exec:5»; (let «object''?*» : (_root_.List (_root_.Option object)) := «eval:7»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «object''?*») = (1 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «object''?*» with | «exec:7» :: «exec:6» => (let object'? : (_root_.Option object) := «exec:7»; (match «exec:6» with | [] => (.bind (.guard (((_root_.Option.isSome object'?) = true))) (fun (_ : Unit) => (match object'? with | some «exec:8» => (let object_id_found : object := «exec:8»; (.pure (((_root_.Option.some object_id_found) : (_root_.Option object))))) | none => .unmatch))) | _ :: _ => .unmatch)) | [] => .unmatch)))))))))))))))))))))


noncomputable def «$find_object_unqualified_e:clause:1» (input0 : arch) (input1 : SpecTec.id) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let ARCH : arch := input0; (let id : SpecTec.id := input1; (.pure ((((_root_.Option.none) : (_root_.Option object)) : (_root_.Option object))))))


noncomputable def «$find_object_unqualified_e_clauses» (input0 : arch) (input1 : id) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_object_unqualified_e:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$find_object_unqualified_e:clause:1»  input0 input1)]


noncomputable def «$update_archState_e:clause:0» (input0 : arch) (input1 : SpecTec.archState) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let ARCH : arch := input0; (let archState : SpecTec.archState := input1; (.pure ((({ ARCH with STATE := archState } : arch) : arch)))))


noncomputable def «$update_archState_e_clauses» (input0 : arch) (input1 : archState) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$update_archState_e:clause:0»  input0 input1)]


noncomputable def «$update_object_qualified_e:clause:0» (input0 : arch) (input1 : SpecTec.objectId) (input2 : SpecTec.object) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let ARCH_0 : arch := input0; (let objectId : SpecTec.objectId := input1; (let object : SpecTec.object := input2; (.bind (.call ⟨(_root_.Option SpecTec.object), SpecTecCall.«$find_object_qualified_e» ARCH_0 objectId⟩) (fun («exec:1» : (_root_.Option SpecTec.object)) => (let «eval:0» : (_root_.Option SpecTec.object) := «exec:1»; (.bind (.guard ((((_root_.Option.none) : (_root_.Option SpecTec.object)) ≠ «eval:0»))) (fun (_ : Unit) => (.bind (.call ⟨arch, SpecTecCall.«$add_object_e» ARCH_0 objectId object⟩) (fun («exec:2» : arch) => (let «eval:1» : arch := «exec:2»; (let ARCH_1 : arch := «eval:1»; (.pure ((ARCH_1 : arch)))))))))))))))


noncomputable def «$update_object_qualified_e_clauses» (input0 : arch) (input1 : objectId) (input2 : object) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$update_object_qualified_e:clause:0»  input0 input1 input2)]


noncomputable def «$update_object_unqualified_e:case_1:pattern-iter:0:clause:0» (input0 : (_root_.List (pair (_root_.List _root_.String) object))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List object)), ([] : (_root_.List objectId))) : ((_root_.List object) × (_root_.List objectId))))) | _ :: _ => .unmatch)


noncomputable def «$update_object_unqualified_e:case_1:pattern-iter:0:clause:1» (input0 : (_root_.List (pair (_root_.List _root_.String) object))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let objectId : SpecTec.objectId := «exec:3»; (let _object : object := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair (_root_.List _root_.String) object)) := «exec:1»; (.bind (.call ⟨((_root_.List object) × (_root_.List SpecTec.objectId)), SpecTecCall.«$update_object_unqualified_e:case_1:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List object) × (_root_.List SpecTec.objectId))) => (let «pattern-tail:1» : (_root_.List object) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.objectId) := («exec:5»).2; (.pure ((((_object :: «pattern-tail:1»), (objectId :: «pattern-tail:2»)) : ((_root_.List object) × (_root_.List SpecTec.objectId))))))))))))) | [] => .unmatch)


noncomputable def «$update_object_unqualified_e:case_1:pattern-iter:0_clauses» (input0 : (_root_.List (pair (_root_.List _root_.String) object))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$update_object_unqualified_e:case_1:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$update_object_unqualified_e:case_1:pattern-iter:0:clause:1»  input0)]


noncomputable def «$update_object_unqualified_e:case_1:iter:2:clause:0» (input0 : SpecTec.id) (input1 : (_root_.List objectId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let id : SpecTec.id := input0; (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.Option objectId))) : (_root_.List (_root_.Option objectId))))) | _ :: _ => .unmatch))


noncomputable def «$update_object_unqualified_e:case_1:iter:2:clause:1» (input0 : SpecTec.id) (input1 : (_root_.List SpecTec.objectId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let id : SpecTec.id := input0; (match input1 with | «exec:2» :: «exec:1» => (let objectId : SpecTec.objectId := «exec:2»; (let «tail:0» : (_root_.List SpecTec.objectId) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$objectId_ends_with» objectId id⟩) (fun («exec:3» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.Option SpecTec.objectId), SpecTecCall.«$ite» (_root_.Option SpecTec.objectId) «eval:3» (_root_.Option.some objectId) ((_root_.Option.none) : (_root_.Option SpecTec.objectId))⟩) (fun («exec:4» : (_root_.Option SpecTec.objectId)) => (let «eval:4» : (_root_.Option SpecTec.objectId) := «exec:4»; (let objectId_id? : (_root_.Option SpecTec.objectId) := «eval:4»; (.bind (.call ⟨(_root_.List (_root_.Option SpecTec.objectId)), SpecTecCall.«$update_object_unqualified_e:case_1:iter:2» id «tail:0»⟩) (fun («exec:5» : (_root_.List (_root_.Option SpecTec.objectId))) => (let «tail:1» : (_root_.List (_root_.Option SpecTec.objectId)) := «exec:5»; (.pure (((objectId_id? :: «tail:1») : (_root_.List (_root_.Option SpecTec.objectId))))))))))))))))) | [] => .unmatch))


noncomputable def «$update_object_unqualified_e:case_1:iter:2_clauses» (input0 : id) (input1 : (_root_.List objectId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$update_object_unqualified_e:case_1:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$update_object_unqualified_e:case_1:iter:2:clause:1»  input0 input1)]


noncomputable def «$update_object_unqualified_e:case_1:iter:5:clause:0» (input0 : (_root_.List (_root_.Option objectId))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$update_object_unqualified_e:case_1:iter:5:clause:1» (input0 : (_root_.List (_root_.Option objectId))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let objectId_id? : (_root_.Option objectId) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option objectId)) := «exec:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$update_object_unqualified_e:case_1:iter:5» «tail:0»⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:3»; (.pure ((((!(_root_.Option.isNone objectId_id?)) :: «tail:1») : (_root_.List _root_.Bool))))))))) | [] => .unmatch)


noncomputable def «$update_object_unqualified_e:case_1:iter:5_clauses» (input0 : (_root_.List (_root_.Option objectId))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$update_object_unqualified_e:case_1:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («$update_object_unqualified_e:case_1:iter:5:clause:1»  input0)]


noncomputable def «$update_object_unqualified_e:clause:0» (input0 : arch) (input1 : SpecTec.id) (input2 : SpecTec.object) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let ARCH_0 : arch := input0; (let id : SpecTec.id := input1; (let object : SpecTec.object := input2; (match (arch.STORE ARCH_0) with | .«`{ % `}» «exec:1» => (let «eval:1» : (_root_.List (pair objectId SpecTec.object)) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.object) × (_root_.List objectId)), SpecTecCall.«$update_object_unqualified_e:case_1:pattern-iter:0» «eval:1»⟩) (fun («exec:2» : ((_root_.List SpecTec.object) × (_root_.List objectId))) => (let «_object*» : (_root_.List SpecTec.object) := («exec:2»).1; (let «objectId*» : (_root_.List objectId) := («exec:2»).2; (.bind (.call ⟨(_root_.List (_root_.Option objectId)), SpecTecCall.«$update_object_unqualified_e:case_1:iter:2» id «objectId*»⟩) (fun («exec:3» : (_root_.List (_root_.Option objectId))) => (let «objectId_id?*» : (_root_.List (_root_.Option objectId)) := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$update_object_unqualified_e:case_1:iter:5» «objectId_id?*»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «eval:6» : (_root_.List _root_.Bool) := «exec:4»; (.bind (.call ⟨(_root_.List (_root_.Option objectId)), SpecTecCall.«$filter_» (_root_.Option objectId) «objectId_id?*» «eval:6»⟩) (fun («exec:5» : (_root_.List (_root_.Option objectId))) => (let «eval:7» : (_root_.List (_root_.Option objectId)) := «exec:5»; (let «objectId''?*» : (_root_.List (_root_.Option objectId)) := «eval:7»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «objectId''?*») = (1 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «objectId''?*» with | «exec:7» :: «exec:6» => (let objectId'? : (_root_.Option objectId) := «exec:7»; (match «exec:6» with | [] => (.bind (.guard (((_root_.Option.isSome objectId'?) = true))) (fun (_ : Unit) => (match objectId'? with | some «exec:8» => (let objectId_found : objectId := «exec:8»; (.bind (.call ⟨arch, SpecTecCall.«$add_object_e» ARCH_0 objectId_found object⟩) (fun («exec:9» : arch) => (let «eval:8» : arch := «exec:9»; (let ARCH_1 : arch := «eval:8»; (.pure ((ARCH_1 : arch)))))))) | none => .unmatch))) | _ :: _ => .unmatch)) | [] => .unmatch))))))))))))))))))))))


noncomputable def «$update_object_unqualified_e_clauses» (input0 : arch) (input1 : id) (input2 : object) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$update_object_unqualified_e:clause:0»  input0 input1 input2)]


noncomputable def «Expr_eval:non-default-abort_2:pattern-iter:1:clause:0» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List typedExpressionIR))) : ((_root_.List nameIR) × (_root_.List typedExpressionIR))))) | _ :: _ => .unmatch)


noncomputable def «Expr_eval:non-default-abort_2:pattern-iter:1:clause:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% '=' %» «exec:3» «exec:4» => (let nameIR : SpecTec.nameIR := «exec:3»; (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:4»; (let «pattern-tail:0» : (_root_.List namedExpressionIR) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR)), SpecTecCall.«Expr_eval:non-default-abort_2:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR))) => (let «pattern-tail:1» : (_root_.List SpecTec.nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.typedExpressionIR) := («exec:5»).2; (.pure ((((nameIR :: «pattern-tail:1»), (typedExpressionIR :: «pattern-tail:2»)) : ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR))))))))))))) | [] => .unmatch)


noncomputable def «Expr_eval:non-default-abort_2:pattern-iter:1_clauses» (input0 : (_root_.List namedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Expr_eval:non-default-abort_2:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Expr_eval:non-default-abort_2:pattern-iter:1:clause:1»  input0)]


noncomputable def «Expr_eval:non-default-cont_2:pattern-iter:1:clause:0» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List typedExpressionIR))) : ((_root_.List nameIR) × (_root_.List typedExpressionIR))))) | _ :: _ => .unmatch)


noncomputable def «Expr_eval:non-default-cont_2:pattern-iter:1:clause:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% '=' %» «exec:3» «exec:4» => (let nameIR : SpecTec.nameIR := «exec:3»; (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:4»; (let «pattern-tail:0» : (_root_.List namedExpressionIR) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR)), SpecTecCall.«Expr_eval:non-default-cont_2:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR))) => (let «pattern-tail:1» : (_root_.List SpecTec.nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.typedExpressionIR) := («exec:5»).2; (.pure ((((nameIR :: «pattern-tail:1»), (typedExpressionIR :: «pattern-tail:2»)) : ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.typedExpressionIR))))))))))))) | [] => .unmatch)

end SpecTec
