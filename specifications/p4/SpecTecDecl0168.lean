import SpecTecDecl0167

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$enter_t_clauses» (input0 : typingContext) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$enter_t:clause:0»  input0)]


noncomputable def «$exit_t:clause:0» (input0 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC : typingContext := input0; (let «typeFrame*» : (_root_.List typeFrame) := (localTypingLayer.FRAMES (typingContext.LOCAL TC)); (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeFrame*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «typeFrame*» with | «exec:2» :: «exec:1» => (let typeFrame_h : typeFrame := «exec:2»; (let «typeFrame_t*» : (_root_.List typeFrame) := «exec:1»; (.pure ((({ TC with LOCAL := ({ (typingContext.LOCAL TC) with FRAMES := «typeFrame_t*» } : localTypingLayer) } : typingContext) : typingContext))))) | [] => .unmatch)))))


noncomputable def «$exit_t_clauses» (input0 : typingContext) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$exit_t:clause:0»  input0)]


noncomputable def «$set_control_t:clause:0» (input0 : typingContext) (input1 : SpecTec.flow) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC : typingContext := input0; (let flow : SpecTec.flow := input1; (.pure ((({ TC with CONTROL := flow } : typingContext) : typingContext)))))


noncomputable def «$set_control_t_clauses» (input0 : typingContext) (input1 : flow) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$set_control_t:clause:0»  input0 input1)]


noncomputable def «$enter_loop_t:clause:0» (input0 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC : typingContext := input0; (.pure ((({ TC with LOOP := ((loop.IN) : loop) } : typingContext) : typingContext))))


noncomputable def «$enter_loop_t_clauses» (input0 : typingContext) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$enter_loop_t:clause:0»  input0)]


noncomputable def «$set_loop_t:clause:0» (input0 : typingContext) (input1 : SpecTec.loop) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC : typingContext := input0; (let loop : SpecTec.loop := input1; (.pure ((({ TC with LOOP := loop } : typingContext) : typingContext)))))


noncomputable def «$set_loop_t_clauses» (input0 : typingContext) (input1 : loop) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$set_loop_t:clause:0»  input0 input1)]


noncomputable def «$add_typeParameters_t:case_1:iter:0:clause:0» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeDefIR)) : (_root_.List typeDefIR)))) | _ :: _ => .unmatch)


noncomputable def «$add_typeParameters_t:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeId : SpecTec.typeId := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeId) := «exec:1»; (.bind (.call ⟨(_root_.List typeDefIR), SpecTecCall.«$add_typeParameters_t:case_1:iter:0» «tail:0»⟩) (fun («exec:3» : (_root_.List typeDefIR)) => (let «tail:1» : (_root_.List typeDefIR) := «exec:3»; (.pure (((((typeDefIR._NAME typeId) : typeDefIR) :: «tail:1») : (_root_.List typeDefIR))))))))) | [] => .unmatch)


noncomputable def «$add_typeParameters_t:case_1:iter:0_clauses» (input0 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_typeParameters_t:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$add_typeParameters_t:case_1:iter:0:clause:1»  input0)]


noncomputable def «$add_callableDef_non_overload_t:case_1:pattern-iter:1:clause:0» (input0 : (_root_.List callTargetId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List (_root_.List id))), ([] : (_root_.List nameIR))) : ((_root_.List (_root_.List id)) × (_root_.List nameIR))))) | _ :: _ => .unmatch)


noncomputable def «$add_callableDef_non_overload_t:case_1:pattern-iter:1:clause:1» (input0 : (_root_.List callTargetId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% `( % `)» «exec:3» «exec:4» => (let nameIR_k : nameIR := «exec:3»; (let «_id'*» : (_root_.List id) := «exec:4»; (let «pattern-tail:0» : (_root_.List callTargetId) := «exec:1»; (.bind (.call ⟨((_root_.List (_root_.List id)) × (_root_.List nameIR)), SpecTecCall.«$add_callableDef_non_overload_t:case_1:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List (_root_.List id)) × (_root_.List nameIR))) => (let «pattern-tail:1» : (_root_.List (_root_.List id)) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List nameIR) := («exec:5»).2; (.pure ((((«_id'*» :: «pattern-tail:1»), (nameIR_k :: «pattern-tail:2»)) : ((_root_.List (_root_.List id)) × (_root_.List nameIR))))))))))))) | [] => .unmatch)


noncomputable def «$add_callableDef_non_overload_t:case_1:pattern-iter:1_clauses» (input0 : (_root_.List callTargetId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_callableDef_non_overload_t:case_1:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$add_callableDef_non_overload_t:case_1:pattern-iter:1:clause:1»  input0)]


noncomputable def «$add_callableDef_non_overload_t:case_2:pattern-iter:1:clause:0» (input0 : (_root_.List callTargetId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List (_root_.List id))), ([] : (_root_.List nameIR))) : ((_root_.List (_root_.List id)) × (_root_.List nameIR))))) | _ :: _ => .unmatch)


noncomputable def «$add_callableDef_non_overload_t:case_2:pattern-iter:1:clause:1» (input0 : (_root_.List callTargetId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% `( % `)» «exec:3» «exec:4» => (let nameIR_k : nameIR := «exec:3»; (let «_id'*» : (_root_.List id) := «exec:4»; (let «pattern-tail:0» : (_root_.List callTargetId) := «exec:1»; (.bind (.call ⟨((_root_.List (_root_.List id)) × (_root_.List nameIR)), SpecTecCall.«$add_callableDef_non_overload_t:case_2:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List (_root_.List id)) × (_root_.List nameIR))) => (let «pattern-tail:1» : (_root_.List (_root_.List id)) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List nameIR) := («exec:5»).2; (.pure ((((«_id'*» :: «pattern-tail:1»), (nameIR_k :: «pattern-tail:2»)) : ((_root_.List (_root_.List id)) × (_root_.List nameIR))))))))))))) | [] => .unmatch)


noncomputable def «$add_callableDef_non_overload_t:case_2:pattern-iter:1_clauses» (input0 : (_root_.List callTargetId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_callableDef_non_overload_t:case_2:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$add_callableDef_non_overload_t:case_2:pattern-iter:1:clause:1»  input0)]


noncomputable def «$add_constructorDef_t:clause:0» (input0 : typingContext) (input1 : SpecTec.callableId) (input2 : SpecTec.constructorTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC : typingContext := input0; (let callableId : SpecTec.callableId := input1; (let constructorTypeDefIR : SpecTec.constructorTypeDefIR := input2; (let constructorTypeDefEnv : SpecTec.constructorTypeDefEnv := (globalTypingLayer.CONSTRUCTOR (typingContext.GLOBAL TC)); (.bind (.call ⟨(set SpecTec.callableId), SpecTecCall.«$dom_map» SpecTec.callableId SpecTec.constructorTypeDefIR constructorTypeDefEnv⟩) (fun («exec:1» : (set SpecTec.callableId)) => (let «eval:0» : (set SpecTec.callableId) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$in_set» SpecTec.callableId callableId «eval:0»⟩) (fun («exec:2» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:2»; (.bind (.guard ((¬ («eval:1» = true)))) (fun (_ : Unit) => (.bind (.call ⟨(map SpecTec.callableId SpecTec.constructorTypeDefIR), SpecTecCall.«$add_map» SpecTec.callableId SpecTec.constructorTypeDefIR constructorTypeDefEnv callableId constructorTypeDefIR⟩) (fun («exec:3» : (map SpecTec.callableId SpecTec.constructorTypeDefIR)) => (let «eval:2» : (map SpecTec.callableId SpecTec.constructorTypeDefIR) := «exec:3»; (let constructorTypeDefEnv_update : SpecTec.constructorTypeDefEnv := «eval:2»; (let TC' : typingContext := ({ TC with GLOBAL := ({ (typingContext.GLOBAL TC) with CONSTRUCTOR := constructorTypeDefEnv_update } : globalTypingLayer) } : typingContext); (.pure ((TC' : typingContext))))))))))))))))))))


noncomputable def «$add_constructorDef_t_clauses» (input0 : typingContext) (input1 : callableId) (input2 : constructorTypeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_constructorDef_t:clause:0»  input0 input1 input2)]


noncomputable def «$add_constructorDef_non_overload_t:case_1:pattern-iter:1:clause:0» (input0 : (_root_.List callTargetId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List (_root_.List id))), ([] : (_root_.List nameIR))) : ((_root_.List (_root_.List id)) × (_root_.List nameIR))))) | _ :: _ => .unmatch)


noncomputable def «$add_constructorDef_non_overload_t:case_1:pattern-iter:1:clause:1» (input0 : (_root_.List callTargetId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% `( % `)» «exec:3» «exec:4» => (let nameIR_k : nameIR := «exec:3»; (let «_id'*» : (_root_.List id) := «exec:4»; (let «pattern-tail:0» : (_root_.List callTargetId) := «exec:1»; (.bind (.call ⟨((_root_.List (_root_.List id)) × (_root_.List nameIR)), SpecTecCall.«$add_constructorDef_non_overload_t:case_1:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List (_root_.List id)) × (_root_.List nameIR))) => (let «pattern-tail:1» : (_root_.List (_root_.List id)) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List nameIR) := («exec:5»).2; (.pure ((((«_id'*» :: «pattern-tail:1»), (nameIR_k :: «pattern-tail:2»)) : ((_root_.List (_root_.List id)) × (_root_.List nameIR))))))))))))) | [] => .unmatch)


noncomputable def «$add_constructorDef_non_overload_t:case_1:pattern-iter:1_clauses» (input0 : (_root_.List callTargetId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_constructorDef_non_overload_t:case_1:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$add_constructorDef_non_overload_t:case_1:pattern-iter:1:clause:1»  input0)]


noncomputable def «$add_constructorDef_non_overload_t:clause:0» (input0 : typingContext) (input1 : SpecTec.callableId) (input2 : SpecTec.constructorTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC : typingContext := input0; (let callableId : SpecTec.callableId := input1; (let constructorTypeDefIR : SpecTec.constructorTypeDefIR := input2; (let constructorTypeDefEnv : SpecTec.constructorTypeDefEnv := (globalTypingLayer.CONSTRUCTOR (typingContext.GLOBAL TC)); (match callableId with | .«% `( % `)» «exec:1» «exec:2» => (let nameIR : SpecTec.nameIR := «exec:1»; (let «_id*» : (_root_.List id) := «exec:2»; (.bind (.call ⟨(set SpecTec.callableId), SpecTecCall.«$dom_map» SpecTec.callableId SpecTec.constructorTypeDefIR constructorTypeDefEnv⟩) (fun («exec:3» : (set SpecTec.callableId)) => (let «eval:0» : (set SpecTec.callableId) := «exec:3»; (match «eval:0» with | .«`{ % `}» «exec:4» => (let «eval:2» : (_root_.List SpecTec.callableId) := «exec:4»; (.bind (.call ⟨((_root_.List (_root_.List id)) × (_root_.List SpecTec.nameIR)), SpecTecCall.«$add_constructorDef_non_overload_t:case_1:pattern-iter:1» «eval:2»⟩) (fun («exec:5» : ((_root_.List (_root_.List id)) × (_root_.List SpecTec.nameIR))) => (let «_id'**» : (_root_.List (_root_.List id)) := («exec:5»).1; (let «nameIR_k*» : (_root_.List SpecTec.nameIR) := («exec:5»).2; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$in_set» SpecTec.nameIR nameIR ((set.«`{ % `}» «nameIR_k*») : (set SpecTec.nameIR))⟩) (fun («exec:6» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:6»; (.bind (.guard ((¬ («eval:3» = true)))) (fun (_ : Unit) => (.bind (.call ⟨(map SpecTec.callableId SpecTec.constructorTypeDefIR), SpecTecCall.«$add_map» SpecTec.callableId SpecTec.constructorTypeDefIR constructorTypeDefEnv callableId constructorTypeDefIR⟩) (fun («exec:7» : (map SpecTec.callableId SpecTec.constructorTypeDefIR)) => (let «eval:4» : (map SpecTec.callableId SpecTec.constructorTypeDefIR) := «exec:7»; (let constructorTypeDefEnv_update : SpecTec.constructorTypeDefEnv := «eval:4»; (let TC' : typingContext := ({ TC with GLOBAL := ({ (typingContext.GLOBAL TC) with CONSTRUCTOR := constructorTypeDefEnv_update } : globalTypingLayer) } : typingContext); (.pure ((TC' : typingContext)))))))))))))))))))))))))))))


noncomputable def «$add_constructorDef_non_overload_t_clauses» (input0 : typingContext) (input1 : callableId) (input2 : constructorTypeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_constructorDef_non_overload_t:clause:0»  input0 input1 input2)]


noncomputable def «$add_constructorDefs_t:clause:0» (input0 : typingContext) (input1 : (_root_.List callableId)) (input2 : (_root_.List constructorTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC : typingContext := input0; (let «callableId*» : (_root_.List callableId) := input1; (let «constructorTypeDefIR*» : (_root_.List constructorTypeDefIR) := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «callableId*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «constructorTypeDefIR*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((TC : typingContext))))))))))


noncomputable def «$add_constructorDefs_t:clause:1» (input0 : typingContext) (input1 : (_root_.List callableId)) (input2 : (_root_.List constructorTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC : typingContext := input0; (let «callableId*» : (_root_.List callableId) := input1; (let «constructorTypeDefIR*» : (_root_.List constructorTypeDefIR) := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «callableId*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «callableId*» with | «exec:2» :: «exec:1» => (let callableId_h : callableId := «exec:2»; (let «callableId_t*» : (_root_.List callableId) := «exec:1»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «constructorTypeDefIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «constructorTypeDefIR*» with | «exec:4» :: «exec:3» => (let constructorTypeDefIR_h : constructorTypeDefIR := «exec:4»; (let «constructorTypeDefIR_t*» : (_root_.List constructorTypeDefIR) := «exec:3»; (.bind (.call ⟨typingContext, SpecTecCall.«$add_constructorDef_t» TC callableId_h constructorTypeDefIR_h⟩) (fun («exec:5» : typingContext) => (let «eval:0» : typingContext := «exec:5»; (let TC' : typingContext := «eval:0»; (.bind (.call ⟨typingContext, SpecTecCall.«$add_constructorDefs_t» TC' «callableId_t*» «constructorTypeDefIR_t*»⟩) (fun («exec:6» : typingContext) => (let «eval:1» : typingContext := «exec:6»; (let TC'' : typingContext := «eval:1»; (.pure ((TC'' : typingContext))))))))))))) | [] => .unmatch))))) | [] => .unmatch))))))


noncomputable def «$add_constructorDefs_t_clauses» (input0 : typingContext) (input1 : (_root_.List callableId)) (input2 : (_root_.List constructorTypeDefIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_constructorDefs_t:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$add_constructorDefs_t:clause:1»  input0 input1 input2)]


noncomputable def «$empty_tableContext:clause:0»  : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let matchPriority : SpecTec.matchPriority := ({ DELTA := (1 : _root_.Nat), LARGEST_WINS := true } : SpecTec.matchPriority); (let matchEntries : SpecTec.matchEntries := ({ SIZE := (0 : _root_.Nat), CONST := true } : SpecTec.matchEntries); (.pure ((({ KEYS := ([] : (_root_.List matchKey)), ACTIONS := ([] : (_root_.List matchAction)), PRIORITIES := matchPriority, ENTRIES := matchEntries, MODE := ((matchMode.NONE) : matchMode) } : tableContext) : tableContext)))))


noncomputable def «$empty_tableContext_clauses» : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$empty_tableContext:clause:0»  )]


noncomputable def «$add_key_tbl:clause:0» (input0 : tableContext) (input1 : SpecTec.id) (input2 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBLC : tableContext := input0; (let id : SpecTec.id := input1; (let typeIR : SpecTec.typeIR := input2; (let matchKey : SpecTec.matchKey := ((SpecTec.matchKey.«% ':' %» typeIR id) : SpecTec.matchKey); (.pure ((({ TBLC with KEYS := ((tableContext.KEYS TBLC) ++ ([matchKey] : (_root_.List SpecTec.matchKey))) } : tableContext) : tableContext)))))))


noncomputable def «$add_key_tbl_clauses» (input0 : tableContext) (input1 : id) (input2 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_key_tbl:clause:0»  input0 input1 input2)]

end SpecTec
