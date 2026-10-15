import SpecTecDecl0155

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$cast_record:case_6:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List id)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$cast_record:case_6:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR_t_field : typeIR := «exec:4»; (let id_t_field : id := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR))), SpecTecCall.«$cast_record:case_6:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List id) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((id_t_field :: «pattern-tail:2»), (typeIR_t_field :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$cast_record:case_6:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$cast_record:case_6:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$cast_record:case_6:pattern-iter:1:clause:1»  input0)]


noncomputable def «$sizeof_minSizeInBits':case_11:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$sizeof_minSizeInBits':case_11:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR : SpecTec.typeIR := «exec:4»; (let _nameIR : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR))), SpecTecCall.«$sizeof_minSizeInBits':case_11:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List SpecTec.typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((_nameIR :: «pattern-tail:2»), (typeIR :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$sizeof_minSizeInBits':case_11:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$sizeof_minSizeInBits':case_11:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$sizeof_minSizeInBits':case_11:pattern-iter:1:clause:1»  input0)]


noncomputable def «$sizeof_minSizeInBits':case_12:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$sizeof_minSizeInBits':case_12:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR : SpecTec.typeIR := «exec:4»; (let _nameIR : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR))), SpecTecCall.«$sizeof_minSizeInBits':case_12:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List SpecTec.typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((_nameIR :: «pattern-tail:2»), (typeIR :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$sizeof_minSizeInBits':case_12:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$sizeof_minSizeInBits':case_12:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$sizeof_minSizeInBits':case_12:pattern-iter:1:clause:1»  input0)]


noncomputable def «$sizeof_minSizeInBits':case_13:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$sizeof_minSizeInBits':case_13:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR : SpecTec.typeIR := «exec:4»; (let _nameIR : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR))), SpecTecCall.«$sizeof_minSizeInBits':case_13:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List SpecTec.typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((_nameIR :: «pattern-tail:2»), (typeIR :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$sizeof_minSizeInBits':case_13:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$sizeof_minSizeInBits':case_13:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$sizeof_minSizeInBits':case_13:pattern-iter:1:clause:1»  input0)]


noncomputable def «$sizeof_maxSizeInBits':case_11:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$sizeof_maxSizeInBits':case_11:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR : SpecTec.typeIR := «exec:4»; (let _nameIR : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR))), SpecTecCall.«$sizeof_maxSizeInBits':case_11:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List SpecTec.typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((_nameIR :: «pattern-tail:2»), (typeIR :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$sizeof_maxSizeInBits':case_11:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':case_11:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':case_11:pattern-iter:1:clause:1»  input0)]


noncomputable def «$sizeof_maxSizeInBits':case_12:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$sizeof_maxSizeInBits':case_12:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR : SpecTec.typeIR := «exec:4»; (let _nameIR : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR))), SpecTecCall.«$sizeof_maxSizeInBits':case_12:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List SpecTec.typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((_nameIR :: «pattern-tail:2»), (typeIR :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$sizeof_maxSizeInBits':case_12:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':case_12:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':case_12:pattern-iter:1:clause:1»  input0)]


noncomputable def «$sizeof_maxSizeInBits':case_13:pattern-iter:1:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$sizeof_maxSizeInBits':case_13:pattern-iter:1:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let typeIR : SpecTec.typeIR := «exec:4»; (let _nameIR : nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR))), SpecTecCall.«$sizeof_maxSizeInBits':case_13:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List SpecTec.typeIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((_nameIR :: «pattern-tail:2»), (typeIR :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))))))))))))))) | [] => .unmatch)


noncomputable def «$sizeof_maxSizeInBits':case_13:pattern-iter:1_clauses» (input0 : (_root_.List fieldTypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':case_13:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':case_13:pattern-iter:1:clause:1»  input0)]


noncomputable def «$type_of_typedExpressionIR:clause:0» (input0 : SpecTec.typedExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typedExpressionIR : SpecTec.typedExpressionIR := input0; (match typedExpressionIR with | .«% '#' %» «exec:1» «exec:2» => (let _expressionIR : expressionIR := «exec:1»; (match «exec:2» with | .«`( % % `)» «exec:3» «exec:4» => (let typeIR : SpecTec.typeIR := «exec:3»; (let _ctk : ctk := «exec:4»; (.pure ((typeIR : SpecTec.typeIR)))))))))


noncomputable def «$type_of_typedExpressionIR_clauses» (input0 : typedExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$type_of_typedExpressionIR:clause:0»  input0)]


noncomputable def «$ctk_of_typedExpressionIR:clause:0» (input0 : SpecTec.typedExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typedExpressionIR : SpecTec.typedExpressionIR := input0; (match typedExpressionIR with | .«% '#' %» «exec:1» «exec:2» => (let _expressionIR : expressionIR := «exec:1»; (match «exec:2» with | .«`( % % `)» «exec:3» «exec:4» => (let _typeIR : typeIR := «exec:3»; (let ctk : SpecTec.ctk := «exec:4»; (.pure ((ctk : SpecTec.ctk)))))))))


noncomputable def «$ctk_of_typedExpressionIR_clauses» (input0 : typedExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$ctk_of_typedExpressionIR:clause:0»  input0)]


noncomputable def «$type_of_typedLvalueIR:clause:0» (input0 : SpecTec.typedLvalueIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typedLvalueIR : SpecTec.typedLvalueIR := input0; (match typedLvalueIR with | .«% '#' %» «exec:1» «exec:2» => (let _lvalueIR : lvalueIR := «exec:1»; (match «exec:2» with | .«`( % `)» «exec:3» => (let typeIR : SpecTec.typeIR := «exec:3»; (.pure ((typeIR : SpecTec.typeIR))))))))


noncomputable def «$type_of_typedLvalueIR_clauses» (input0 : typedLvalueIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$type_of_typedLvalueIR:clause:0»  input0)]


noncomputable def «$flatten_objectInitializerOptIR:clause:0» (input0 : objectInitializerOptIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let objectInitializerIR? : (_root_.Option objectInitializerIR) := input0; (.bind (.guard (((_root_.Option.isNone objectInitializerIR?) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List objectDeclarationIR)) : objectDeclarationListIR))))))


noncomputable def «$flatten_objectInitializerOptIR:clause:1» (input0 : SpecTec.objectInitializerOptIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let objectInitializerOptIR : SpecTec.objectInitializerOptIR := input0; (.bind (.guard (((_root_.Option.isSome objectInitializerOptIR) = true))) (fun (_ : Unit) => (match objectInitializerOptIR with | some «exec:1» => (match «exec:1» with | .«'=' `{ % `}» «exec:2» => (let objectDeclarationListIR : SpecTec.objectDeclarationListIR := «exec:2»; (.pure ((objectDeclarationListIR : SpecTec.objectDeclarationListIR))))) | none => .unmatch))))


noncomputable def «$flatten_objectInitializerOptIR_clauses» (input0 : objectInitializerOptIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_objectInitializerOptIR:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_objectInitializerOptIR:clause:1»  input0)]


noncomputable def «$tableEntryPriorityOptIR_of_tableEntryIR:clause:0» (input0 : SpecTec.tableEntryIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableEntryIR : SpecTec.tableEntryIR := input0; (match tableEntryIR with | .«% % % ':' % % ';'» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let _constOptIR : constOptIR := «exec:1»; (let tableEntryPriorityOptIR : SpecTec.tableEntryPriorityOptIR := «exec:2»; (let _keysetExpressionIR : keysetExpressionIR := «exec:3»; (let _tableActionReferenceIR : tableActionReferenceIR := «exec:4»; (let _annotationList : annotationList := «exec:5»; (.pure ((tableEntryPriorityOptIR : SpecTec.tableEntryPriorityOptIR))))))))))


noncomputable def «$tableEntryPriorityOptIR_of_tableEntryIR_clauses» (input0 : tableEntryIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$tableEntryPriorityOptIR_of_tableEntryIR:clause:0»  input0)]

end SpecTec
