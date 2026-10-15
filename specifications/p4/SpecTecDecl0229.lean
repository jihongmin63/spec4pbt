import SpecTecDecl0228

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$tableObject_create_entry_keys:case_2:pattern-iter:0:clause:1» (input0 : (_root_.List (_root_.String × (_root_.String × typeIR)))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_key_t : nameIR := («exec:2»).1; (let nameIR_matchKind_t : nameIR := ((«exec:2»).2).1; (let typeIR_t : typeIR := ((«exec:2»).2).2; (let «pattern-tail:0» : (_root_.List (_root_.String × (_root_.String × typeIR))) := «exec:1»; (.bind (.call ⟨((_root_.List nameIR) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$tableObject_create_entry_keys:case_2:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:3» : ((_root_.List nameIR) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «pattern-tail:1» : (_root_.List nameIR) := («exec:3»).1; (let «pattern-tail:2» : (_root_.List nameIR) := ((«exec:3»).2).1; (let «pattern-tail:3» : (_root_.List typeIR) := ((«exec:3»).2).2; (.pure ((((nameIR_key_t :: «pattern-tail:1»), ((nameIR_matchKind_t :: «pattern-tail:2»), (typeIR_t :: «pattern-tail:3»))) : ((_root_.List nameIR) × ((_root_.List nameIR) × (_root_.List typeIR))))))))))))))) | [] => .unmatch)


noncomputable def «$tableObject_create_entry_keys:case_2:pattern-iter:0_clauses» (input0 : (_root_.List (_root_.String × (_root_.String × typeIR)))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$tableObject_create_entry_keys:case_2:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$tableObject_create_entry_keys:case_2:pattern-iter:0:clause:1»  input0)]


noncomputable def «$tableObject_create_entry_keys:case_2:iter:3:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List (_root_.String × (_root_.String × typeIR)))) : (_root_.List (_root_.String × (_root_.String × typeIR)))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$tableObject_create_entry_keys:case_2:iter:3:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_key_t : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_matchKind_t : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (match input2 with | «exec:6» :: «exec:5» => (let typeIR_t : typeIR := «exec:6»; (let «tail:2» : (_root_.List typeIR) := «exec:5»; (.bind (.call ⟨(_root_.List (_root_.String × (_root_.String × typeIR))), SpecTecCall.«$tableObject_create_entry_keys:case_2:iter:3» «tail:0» «tail:1» «tail:2»⟩) (fun («exec:7» : (_root_.List (_root_.String × (_root_.String × typeIR)))) => (let «tail:3» : (_root_.List (_root_.String × (_root_.String × typeIR))) := «exec:7»; (.pure ((((nameIR_key_t, (nameIR_matchKind_t, typeIR_t)) :: «tail:3») : (_root_.List (_root_.String × (_root_.String × typeIR))))))))))) | [] => .unmatch))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$tableObject_create_entry_keys:case_2:iter:3_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$tableObject_create_entry_keys:case_2:iter:3:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$tableObject_create_entry_keys:case_2:iter:3:clause:1»  input0 input1 input2)]


noncomputable def «$interface_of_tableKeyIR:clause:0» (input0 : tableKeyIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% '#' % ':' % % ';'» «exec:1» «exec:2» «exec:3» «exec:4» => (let typedExpressionIR : SpecTec.typedExpressionIR := «exec:1»; (let nameIR_key : nameIR := «exec:2»; (let nameIR_matchKind : nameIR := «exec:3»; (let annotationList : SpecTec.annotationList := «exec:4»; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$type_of_typedExpressionIR» typedExpressionIR⟩) (fun («exec:5» : SpecTec.typeIR) => (let «eval:0» : SpecTec.typeIR := «exec:5»; (let typeIR : SpecTec.typeIR := «eval:0»; (.pure (((nameIR_key, (nameIR_matchKind, typeIR)) : (nameIR × (nameIR × SpecTec.typeIR))))))))))))))


noncomputable def «$interface_of_tableKeyIR_clauses» (input0 : tableKeyIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$interface_of_tableKeyIR:clause:0»  input0)]


noncomputable def «$key_interface_of_tableObject:case_1:iter:0:clause:0» (input0 : (_root_.List tableKeyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List nameIR) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$key_interface_of_tableObject:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.tableKeyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableKeyIR : SpecTec.tableKeyIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableKeyIR) := «exec:1»; (.bind (.call ⟨(nameIR × (nameIR × SpecTec.typeIR)), SpecTecCall.«$interface_of_tableKeyIR» tableKeyIR⟩) (fun («exec:3» : (nameIR × (nameIR × SpecTec.typeIR))) => (let «eval:1» : (nameIR × (nameIR × SpecTec.typeIR)) := «exec:3»; (let nameIR_key : nameIR := («eval:1»).1; (let nameIR_matchKind : nameIR := ((«eval:1»).2).1; (let typeIR : SpecTec.typeIR := ((«eval:1»).2).2; (.bind (.call ⟨((_root_.List nameIR) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR))), SpecTecCall.«$key_interface_of_tableObject:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : ((_root_.List nameIR) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))) => (let «tail:1» : (_root_.List nameIR) := («exec:4»).1; (let «tail:2» : (_root_.List nameIR) := ((«exec:4»).2).1; (let «tail:3» : (_root_.List SpecTec.typeIR) := ((«exec:4»).2).2; (.pure ((((nameIR_key :: «tail:1»), ((nameIR_matchKind :: «tail:2»), (typeIR :: «tail:3»))) : ((_root_.List nameIR) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR))))))))))))))))))) | [] => .unmatch)


noncomputable def «$key_interface_of_tableObject:case_1:iter:0_clauses» (input0 : (_root_.List tableKeyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$key_interface_of_tableObject:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$key_interface_of_tableObject:case_1:iter:0:clause:1»  input0)]


noncomputable def «$key_interface_of_tableObject:case_1:iter:2:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List (_root_.String × (_root_.String × typeIR)))) : (_root_.List (_root_.String × (_root_.String × typeIR)))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$key_interface_of_tableObject:case_1:iter:2:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_key : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_matchKind : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (match input2 with | «exec:6» :: «exec:5» => (let typeIR : SpecTec.typeIR := «exec:6»; (let «tail:2» : (_root_.List SpecTec.typeIR) := «exec:5»; (.bind (.call ⟨(_root_.List (_root_.String × (_root_.String × SpecTec.typeIR))), SpecTecCall.«$key_interface_of_tableObject:case_1:iter:2» «tail:0» «tail:1» «tail:2»⟩) (fun («exec:7» : (_root_.List (_root_.String × (_root_.String × SpecTec.typeIR)))) => (let «tail:3» : (_root_.List (_root_.String × (_root_.String × SpecTec.typeIR))) := «exec:7»; (.pure ((((nameIR_key, (nameIR_matchKind, typeIR)) :: «tail:3») : (_root_.List (_root_.String × (_root_.String × SpecTec.typeIR))))))))))) | [] => .unmatch))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$key_interface_of_tableObject:case_1:iter:2_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$key_interface_of_tableObject:case_1:iter:2:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$key_interface_of_tableObject:case_1:iter:2:clause:1»  input0 input1 input2)]


noncomputable def «$key_interface_of_tableObject:clause:0» (input0 : tableObject) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«TABLE % `{ % % `}» «exec:1» «exec:2» «exec:3» => (let typeId : SpecTec.typeId := «exec:1»; (let frame : SpecTec.frame := «exec:2»; (let TBL : tableObjectProperty := «exec:3»; (match (tableObjectProperty.KEYS TBL) with | .«KEY '=' `{ % `}» «exec:4» => (let «tableKeyIR*» : (_root_.List tableKeyIR) := «exec:4»; (.bind (.call ⟨((_root_.List nameIR) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$key_interface_of_tableObject:case_1:iter:0» «tableKeyIR*»⟩) (fun («exec:5» : ((_root_.List nameIR) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «nameIR_key*» : (_root_.List nameIR) := («exec:5»).1; (let «nameIR_matchKind*» : (_root_.List nameIR) := ((«exec:5»).2).1; (let «typeIR*» : (_root_.List typeIR) := ((«exec:5»).2).2; (.bind (.call ⟨(_root_.List (_root_.String × (_root_.String × typeIR))), SpecTecCall.«$key_interface_of_tableObject:case_1:iter:2» «nameIR_key*» «nameIR_matchKind*» «typeIR*»⟩) (fun («exec:6» : (_root_.List (_root_.String × (_root_.String × typeIR)))) => (let «eval:3» : (_root_.List (nameIR × (nameIR × typeIR))) := «exec:6»; (.pure ((«eval:3» : (_root_.List (nameIR × (nameIR × typeIR))))))))))))))))))))


noncomputable def «$key_interface_of_tableObject_clauses» (input0 : tableObject) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$key_interface_of_tableObject:clause:0»  input0)]


noncomputable def «$tableObject_create_entry_keyset:case_1:iter:0:clause:0» (input0 : (_root_.List tableKeyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), (([] : (_root_.List nameIR)), ([] : (_root_.List typeIR)))) : ((_root_.List nameIR) × ((_root_.List nameIR) × (_root_.List typeIR)))))) | _ :: _ => .unmatch)


noncomputable def «$tableObject_create_entry_keyset:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.tableKeyIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableKeyIR : SpecTec.tableKeyIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableKeyIR) := «exec:1»; (.bind (.call ⟨(nameIR × (nameIR × SpecTec.typeIR)), SpecTecCall.«$interface_of_tableKeyIR» tableKeyIR⟩) (fun («exec:3» : (nameIR × (nameIR × SpecTec.typeIR))) => (let «eval:1» : (nameIR × (nameIR × SpecTec.typeIR)) := «exec:3»; (let nameIR_key : nameIR := («eval:1»).1; (let nameIR_matchKind : nameIR := ((«eval:1»).2).1; (let typeIR : SpecTec.typeIR := ((«eval:1»).2).2; (.bind (.call ⟨((_root_.List nameIR) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR))), SpecTecCall.«$tableObject_create_entry_keyset:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : ((_root_.List nameIR) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR)))) => (let «tail:1» : (_root_.List nameIR) := («exec:4»).1; (let «tail:2» : (_root_.List nameIR) := ((«exec:4»).2).1; (let «tail:3» : (_root_.List SpecTec.typeIR) := ((«exec:4»).2).2; (.pure ((((nameIR_key :: «tail:1»), ((nameIR_matchKind :: «tail:2»), (typeIR :: «tail:3»))) : ((_root_.List nameIR) × ((_root_.List nameIR) × (_root_.List SpecTec.typeIR))))))))))))))))))) | [] => .unmatch)


noncomputable def «$tableObject_create_entry_keyset:case_1:iter:0_clauses» (input0 : (_root_.List tableKeyIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$tableObject_create_entry_keyset:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$tableObject_create_entry_keyset:case_1:iter:0:clause:1»  input0)]


noncomputable def «$tableObject_create_entry_keyset:case_1:iter:2:clause:0» (input0 : (_root_.List tableKeyInterface)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List tableKeyValueInterface))) : ((_root_.List nameIR) × (_root_.List tableKeyValueInterface))))) | _ :: _ => .unmatch)


noncomputable def «$tableObject_create_entry_keyset:case_1:iter:2:clause:1» (input0 : (_root_.List SpecTec.tableKeyInterface)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableKeyInterface : SpecTec.tableKeyInterface := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableKeyInterface) := «exec:1»; (let nameIR_key_update : nameIR := (tableKeyInterface).1; (let tableKeyValueInterface_update : tableKeyValueInterface := (tableKeyInterface).2; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List tableKeyValueInterface)), SpecTecCall.«$tableObject_create_entry_keyset:case_1:iter:2» «tail:0»⟩) (fun («exec:3» : ((_root_.List nameIR) × (_root_.List tableKeyValueInterface))) => (let «tail:1» : (_root_.List nameIR) := («exec:3»).1; (let «tail:2» : (_root_.List tableKeyValueInterface) := («exec:3»).2; (.pure ((((nameIR_key_update :: «tail:1»), (tableKeyValueInterface_update :: «tail:2»)) : ((_root_.List nameIR) × (_root_.List tableKeyValueInterface))))))))))))) | [] => .unmatch)


noncomputable def «$tableObject_create_entry_keyset:case_1:iter:2_clauses» (input0 : (_root_.List tableKeyInterface)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$tableObject_create_entry_keyset:case_1:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$tableObject_create_entry_keyset:case_1:iter:2:clause:1»  input0)]


noncomputable def «$tableObject_create_entry_keyset:case_1:iter:3:clause:0» (input0 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$tableObject_create_entry_keyset:case_1:iter:3:clause:1» (input0 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_matchKind : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$tableObject_create_entry_keyset:case_1:iter:3» «tail:0»⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:3»; (.pure ((((_root_.Decidable.decide (nameIR_matchKind ≠ "selector")) :: «tail:1») : (_root_.List _root_.Bool))))))))) | [] => .unmatch)


noncomputable def «$tableObject_create_entry_keyset:case_1:iter:3_clauses» (input0 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$tableObject_create_entry_keyset:case_1:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$tableObject_create_entry_keyset:case_1:iter:3:clause:1»  input0)]


noncomputable def «$tableObject_create_entry_keyset:case_1:iter:7:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (match input2 with | [] => (.pure ((([] : (_root_.List (_root_.String × (_root_.String × typeIR)))) : (_root_.List (_root_.String × (_root_.String × typeIR)))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$tableObject_create_entry_keyset:case_1:iter:7:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_key : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_matchKind : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (match input2 with | «exec:6» :: «exec:5» => (let typeIR : SpecTec.typeIR := «exec:6»; (let «tail:2» : (_root_.List SpecTec.typeIR) := «exec:5»; (.bind (.call ⟨(_root_.List (_root_.String × (_root_.String × SpecTec.typeIR))), SpecTecCall.«$tableObject_create_entry_keyset:case_1:iter:7» «tail:0» «tail:1» «tail:2»⟩) (fun («exec:7» : (_root_.List (_root_.String × (_root_.String × SpecTec.typeIR)))) => (let «tail:3» : (_root_.List (_root_.String × (_root_.String × SpecTec.typeIR))) := «exec:7»; (.pure ((((nameIR_key, (nameIR_matchKind, typeIR)) :: «tail:3») : (_root_.List (_root_.String × (_root_.String × SpecTec.typeIR))))))))))) | [] => .unmatch))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$tableObject_create_entry_keyset:case_1:iter:7_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$tableObject_create_entry_keyset:case_1:iter:7:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$tableObject_create_entry_keyset:case_1:iter:7:clause:1»  input0 input1 input2)]


noncomputable def «$alias_to_original_lookup_map:case_1:iter:0:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List direction)), (([] : (_root_.List parameterInitializerOptIR)), (([] : (_root_.List typeIR)), (([] : (_root_.List annotationList)), ([] : (_root_.List id)))))) : ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × ((_root_.List annotationList) × (_root_.List id)))))))) | _ :: _ => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (match parameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let annotationList : SpecTec.annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let _typeIR : typeIR := «exec:5»; (let id : SpecTec.id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × ((_root_.List SpecTec.annotationList) × (_root_.List SpecTec.id))))), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:0» «tail:0»⟩) (fun («exec:8» : ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × ((_root_.List SpecTec.annotationList) × (_root_.List SpecTec.id)))))) => (let «tail:1» : (_root_.List direction) := («exec:8»).1; (let «tail:2» : (_root_.List parameterInitializerOptIR) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List typeIR) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List SpecTec.annotationList) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List SpecTec.id) := ((((«exec:8»).2).2).2).2; (.pure ((((_direction :: «tail:1»), ((_parameterInitializerOptIR :: «tail:2»), ((_typeIR :: «tail:3»), ((annotationList :: «tail:4»), (id :: «tail:5»))))) : ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × ((_root_.List SpecTec.annotationList) × (_root_.List SpecTec.id))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:0_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:0:clause:1»  input0)]


noncomputable def «$alias_to_original_lookup_map:case_1:iter:7:clause:0» (input0 : (_root_.List (_root_.Option nameIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List nameIR))) : (_root_.List (_root_.List nameIR))))) | _ :: _ => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:7:clause:1» (input0 : (_root_.List (_root_.Option nameIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_names_opt? : (_root_.Option nameIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option nameIR)) := «exec:1»; (.bind (.call ⟨(_root_.List nameIR), SpecTecCall.«$opt_as_seq_» nameIR nameIR_names_opt?⟩) (fun («exec:3» : (_root_.List nameIR)) => (let «eval:8» : (_root_.List nameIR) := «exec:3»; (let «nameIR_names_seq*» : (_root_.List nameIR) := «eval:8»; (.bind (.call ⟨(_root_.List (_root_.List nameIR)), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:7» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List nameIR))) => (let «tail:1» : (_root_.List (_root_.List nameIR)) := «exec:4»; (.pure (((«nameIR_names_seq*» :: «tail:1») : (_root_.List (_root_.List nameIR)))))))))))))) | [] => .unmatch)

end SpecTec
