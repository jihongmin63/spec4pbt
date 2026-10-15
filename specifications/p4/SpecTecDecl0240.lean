import SpecTecDecl0239

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Cast_impl_neq:headerTypeIR_4:iter:21_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:headerTypeIR_4:iter:21:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:headerTypeIR_4:iter:21:clause:1»  input0)]


noncomputable def «Cast_impl_neq:structTypeIR_4:iter:21:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:structTypeIR_4:iter:21:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (.bind (.guard (((«exec:match:castResult:OK» castResult) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:structTypeIR_4:iter:21» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:structTypeIR_4:iter:21_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:structTypeIR_4:iter:21:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:structTypeIR_4:iter:21:clause:1»  input0)]


noncomputable def «Cast_impl_neq:headerTypeIR_5:iter:21:clause:0» (input0 : (_root_.List castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Cast_impl_neq:headerTypeIR_5:iter:21:clause:1» (input0 : (_root_.List SpecTec.castResult)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let castResult : SpecTec.castResult := «exec:2»; (let «tail:0» : (_root_.List SpecTec.castResult) := «exec:1»; (.bind (.guard (((«exec:match:castResult:OK» castResult) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Cast_impl_neq:headerTypeIR_5:iter:21» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Cast_impl_neq:headerTypeIR_5:iter:21_clauses» (input0 : (_root_.List castResult)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Cast_impl_neq:headerTypeIR_5:iter:21:clause:0»  input0), fun (_ : _root_.Unit) => («Cast_impl_neq:headerTypeIR_5:iter:21:clause:1»  input0)]


noncomputable def «$flatten_controlLocalDeclarationList:clause:0» (input0 : SpecTec.controlLocalDeclarationList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let controlLocalDeclarationList : SpecTec.controlLocalDeclarationList := input0; (.bind (.guard (((«exec:match:controlLocalDeclarationList:_EMPTY» controlLocalDeclarationList) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List controlLocalDeclaration)) : (_root_.List controlLocalDeclaration)))))))


noncomputable def «$flatten_controlLocalDeclarationList:clause:1» (input0 : SpecTec.controlLocalDeclarationList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let controlLocalDeclarationList' : SpecTec.controlLocalDeclarationList := input0; (.bind (.guard (((«exec:match:controlLocalDeclarationList:% %» controlLocalDeclarationList') = true))) (fun (_ : Unit) => (match controlLocalDeclarationList' with | .«% %» «exec:1» «exec:2» => (let controlLocalDeclarationList : SpecTec.controlLocalDeclarationList := «exec:1»; (let controlLocalDeclaration : SpecTec.controlLocalDeclaration := «exec:2»; (.bind (.call ⟨(_root_.List SpecTec.controlLocalDeclaration), SpecTecCall.«$flatten_controlLocalDeclarationList» controlLocalDeclarationList⟩) (fun («exec:3» : (_root_.List SpecTec.controlLocalDeclaration)) => (let «eval:0» : (_root_.List SpecTec.controlLocalDeclaration) := «exec:3»; (.pure (((«eval:0» ++ ([controlLocalDeclaration] : (_root_.List SpecTec.controlLocalDeclaration))) : (_root_.List SpecTec.controlLocalDeclaration))))))))) | _ => .unmatch))))


noncomputable def «$flatten_controlLocalDeclarationList_clauses» (input0 : controlLocalDeclarationList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_controlLocalDeclarationList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_controlLocalDeclarationList:clause:1»  input0)]


noncomputable def «$join_ctk:clause:0» (input0 : SpecTec.ctk) (input1 : SpecTec.ctk) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let ctk : SpecTec.ctk := input0; (let ctk' : SpecTec.ctk := input1; (.bind (.guard (((«exec:match:ctk:LCTK» ctk) = true))) (fun (_ : Unit) => (.bind (.guard (((«exec:match:ctk:LCTK» ctk') = true))) (fun (_ : Unit) => (.pure ((((SpecTec.ctk.LCTK) : SpecTec.ctk) : SpecTec.ctk)))))))))


noncomputable def «$join_ctk:clause:1» (input0 : SpecTec.ctk) (input1 : SpecTec.ctk) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let ctk : SpecTec.ctk := input0; (let ctk' : SpecTec.ctk := input1; (.bind (.guard (((«exec:match:ctk:LCTK» ctk) = true))) (fun (_ : Unit) => (.bind (.guard (((«exec:match:ctk:CTK» ctk') = true))) (fun (_ : Unit) => (.pure ((((SpecTec.ctk.CTK) : SpecTec.ctk) : SpecTec.ctk)))))))))


noncomputable def «$join_ctk:clause:2» (input0 : SpecTec.ctk) (input1 : SpecTec.ctk) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let ctk : SpecTec.ctk := input0; (let ctk' : SpecTec.ctk := input1; (.bind (.guard (((«exec:match:ctk:CTK» ctk) = true))) (fun (_ : Unit) => (.bind (.guard (((«exec:match:ctk:LCTK» ctk') = true))) (fun (_ : Unit) => (.pure ((((SpecTec.ctk.CTK) : SpecTec.ctk) : SpecTec.ctk)))))))))


noncomputable def «$join_ctk:clause:3» (input0 : SpecTec.ctk) (input1 : SpecTec.ctk) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let ctk : SpecTec.ctk := input0; (let ctk' : SpecTec.ctk := input1; (.bind (.guard (((«exec:match:ctk:CTK» ctk) = true))) (fun (_ : Unit) => (.bind (.guard (((«exec:match:ctk:CTK» ctk') = true))) (fun (_ : Unit) => (.pure ((((SpecTec.ctk.CTK) : SpecTec.ctk) : SpecTec.ctk)))))))))


noncomputable def «$join_ctk:clause:4» (input0 : ctk) (input1 : ctk) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let ctk_a : ctk := input0; (let ctk_b : ctk := input1; (.pure ((((ctk.DYN) : ctk) : ctk)))))


noncomputable def «$join_ctk_clauses» (input0 : ctk) (input1 : ctk) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$join_ctk:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$join_ctk:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$join_ctk:clause:2»  input0 input1), fun (_ : _root_.Unit) => («$join_ctk:clause:3»  input0 input1), fun (_ : _root_.Unit) => («$join_ctk:clause:4»  input0 input1)]


noncomputable def «$joins_ctk:clause:0» (input0 : (_root_.List ctk)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «ctk*» : (_root_.List ctk) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «ctk*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((((ctk.LCTK) : ctk) : ctk))))))


noncomputable def «$joins_ctk:clause:1» (input0 : (_root_.List SpecTec.ctk)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «ctk'*» : (_root_.List SpecTec.ctk) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «ctk'*») = (1 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «ctk'*» with | «exec:2» :: «exec:1» => (let ctk : SpecTec.ctk := «exec:2»; (match «exec:1» with | [] => (.pure ((ctk : SpecTec.ctk))) | _ :: _ => .unmatch)) | [] => .unmatch))))


noncomputable def «$joins_ctk:clause:2» (input0 : (_root_.List ctk)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «ctk'*» : (_root_.List ctk) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «ctk'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «ctk'*» with | «exec:2» :: «exec:1» => (let ctk_a : ctk := «exec:2»; (let «ctk*» : (_root_.List ctk) := «exec:1»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «ctk*») = (1 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «ctk*» with | «exec:4» :: «exec:3» => (let ctk_b : ctk := «exec:4»; (match «exec:3» with | [] => (.bind (.call ⟨ctk, SpecTecCall.«$join_ctk» ctk_a ctk_b⟩) (fun («exec:5» : ctk) => (let «eval:0» : ctk := «exec:5»; (.pure ((«eval:0» : ctk)))))) | _ :: _ => .unmatch)) | [] => .unmatch))))) | [] => .unmatch))))


noncomputable def «$joins_ctk:clause:3» (input0 : (_root_.List ctk)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «ctk'*» : (_root_.List ctk) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «ctk'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «ctk'*» with | «exec:2» :: «exec:1» => (let ctk_a : ctk := «exec:2»; (let «ctk*» : (_root_.List ctk) := «exec:1»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «ctk*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «ctk*» with | «exec:4» :: «exec:3» => (let ctk_b : ctk := «exec:4»; (let «ctk_c*» : (_root_.List ctk) := «exec:3»; (.bind (.guard ((«ctk_c*» ≠ ([] : (_root_.List ctk))))) (fun (_ : Unit) => (.bind (.call ⟨ctk, SpecTecCall.«$join_ctk» ctk_a ctk_b⟩) (fun («exec:5» : ctk) => (let «eval:0» : ctk := «exec:5»; (let ctk_d : ctk := «eval:0»; (.bind (.call ⟨ctk, SpecTecCall.«$joins_ctk» (ctk_d :: «ctk_c*»)⟩) (fun («exec:6» : ctk) => (let «eval:1» : ctk := «exec:6»; (.pure ((«eval:1» : ctk)))))))))))))) | [] => .unmatch))))) | [] => .unmatch))))


noncomputable def «$joins_ctk_clauses» (input0 : (_root_.List ctk)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$joins_ctk:clause:0»  input0), fun (_ : _root_.Unit) => («$joins_ctk:clause:1»  input0), fun (_ : _root_.Unit) => («$joins_ctk:clause:2»  input0), fun (_ : _root_.Unit) => («$joins_ctk:clause:3»  input0)]


noncomputable def «$add_callableDef_overload_t:clause:0» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.callableId) (input3 : SpecTec.callableTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let callableId : SpecTec.callableId := input2; (let callableTypeDefIR : SpecTec.callableTypeDefIR := input3; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (let callableTypeDefEnv : SpecTec.callableTypeDefEnv := (globalTypingLayer.CALLABLE (typingContext.GLOBAL TC)); (.bind (.call ⟨(set SpecTec.callableId), SpecTecCall.«$dom_map» SpecTec.callableId SpecTec.callableTypeDefIR callableTypeDefEnv⟩) (fun («exec:1» : (set SpecTec.callableId)) => (let «eval:0» : (set SpecTec.callableId) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$in_set» SpecTec.callableId callableId «eval:0»⟩) (fun («exec:2» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:2»; (.bind (.guard ((¬ («eval:1» = true)))) (fun (_ : Unit) => (.bind (.call ⟨(map SpecTec.callableId SpecTec.callableTypeDefIR), SpecTecCall.«$add_map» SpecTec.callableId SpecTec.callableTypeDefIR callableTypeDefEnv callableId callableTypeDefIR⟩) (fun («exec:3» : (map SpecTec.callableId SpecTec.callableTypeDefIR)) => (let «eval:2» : (map SpecTec.callableId SpecTec.callableTypeDefIR) := «exec:3»; (let callableTypeDefEnv_update : SpecTec.callableTypeDefEnv := «eval:2»; (let TC' : typingContext := ({ TC with GLOBAL := ({ (typingContext.GLOBAL TC) with CALLABLE := callableTypeDefEnv_update } : globalTypingLayer) } : typingContext); (.pure ((TC' : typingContext)))))))))))))))))))))))


noncomputable def «$add_callableDef_overload_t:clause:1» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.callableId) (input3 : SpecTec.callableTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let callableId : SpecTec.callableId := input2; (let callableTypeDefIR : SpecTec.callableTypeDefIR := input3; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (let callableTypeDefEnv : SpecTec.callableTypeDefEnv := (blockTypingLayer.CALLABLE (typingContext.BLOCK TC)); (.bind (.call ⟨(set SpecTec.callableId), SpecTecCall.«$dom_map» SpecTec.callableId SpecTec.callableTypeDefIR callableTypeDefEnv⟩) (fun («exec:1» : (set SpecTec.callableId)) => (let «eval:0» : (set SpecTec.callableId) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$in_set» SpecTec.callableId callableId «eval:0»⟩) (fun («exec:2» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:2»; (.bind (.guard ((¬ («eval:1» = true)))) (fun (_ : Unit) => (.bind (.call ⟨(map SpecTec.callableId SpecTec.callableTypeDefIR), SpecTecCall.«$add_map» SpecTec.callableId SpecTec.callableTypeDefIR callableTypeDefEnv callableId callableTypeDefIR⟩) (fun («exec:3» : (map SpecTec.callableId SpecTec.callableTypeDefIR)) => (let «eval:2» : (map SpecTec.callableId SpecTec.callableTypeDefIR) := «exec:3»; (let callableTypeDefEnv_update : SpecTec.callableTypeDefEnv := «eval:2»; (let TC' : typingContext := ({ TC with BLOCK := ({ (typingContext.BLOCK TC) with CALLABLE := callableTypeDefEnv_update } : blockTypingLayer) } : typingContext); (.pure ((TC' : typingContext)))))))))))))))))))))))


noncomputable def «$add_callableDef_overload_t_clauses» (input0 : cursor) (input1 : typingContext) (input2 : callableId) (input3 : callableTypeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_callableDef_overload_t:clause:0»  input0 input1 input2 input3), fun (_ : _root_.Unit) => («$add_callableDef_overload_t:clause:1»  input0 input1 input2 input3)]


noncomputable def «$add_callableDef_non_overload_t:clause:0» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.callableId) (input3 : SpecTec.callableTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let callableId : SpecTec.callableId := input2; (let callableTypeDefIR : SpecTec.callableTypeDefIR := input3; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (let callableTypeDefEnv : SpecTec.callableTypeDefEnv := (globalTypingLayer.CALLABLE (typingContext.GLOBAL TC)); (match callableId with | .«% `( % `)» «exec:1» «exec:2» => (let nameIR : SpecTec.nameIR := «exec:1»; (let «_id*» : (_root_.List id) := «exec:2»; (.bind (.call ⟨(set SpecTec.callableId), SpecTecCall.«$dom_map» SpecTec.callableId SpecTec.callableTypeDefIR callableTypeDefEnv⟩) (fun («exec:3» : (set SpecTec.callableId)) => (let «eval:0» : (set SpecTec.callableId) := «exec:3»; (match «eval:0» with | .«`{ % `}» «exec:4» => (let «eval:2» : (_root_.List SpecTec.callableId) := «exec:4»; (.bind (.call ⟨((_root_.List (_root_.List id)) × (_root_.List SpecTec.nameIR)), SpecTecCall.«$add_callableDef_non_overload_t:case_1:pattern-iter:1» «eval:2»⟩) (fun («exec:5» : ((_root_.List (_root_.List id)) × (_root_.List SpecTec.nameIR))) => (let «_id'**» : (_root_.List (_root_.List id)) := («exec:5»).1; (let «nameIR_k*» : (_root_.List SpecTec.nameIR) := («exec:5»).2; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$in_set» SpecTec.nameIR nameIR ((set.«`{ % `}» «nameIR_k*») : (set SpecTec.nameIR))⟩) (fun («exec:6» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:6»; (.bind (.guard ((¬ («eval:3» = true)))) (fun (_ : Unit) => (.bind (.call ⟨(map SpecTec.callableId SpecTec.callableTypeDefIR), SpecTecCall.«$add_map» SpecTec.callableId SpecTec.callableTypeDefIR callableTypeDefEnv callableId callableTypeDefIR⟩) (fun («exec:7» : (map SpecTec.callableId SpecTec.callableTypeDefIR)) => (let «eval:4» : (map SpecTec.callableId SpecTec.callableTypeDefIR) := «exec:7»; (let callableTypeDefEnv_update : SpecTec.callableTypeDefEnv := «eval:4»; (let TC' : typingContext := ({ TC with GLOBAL := ({ (typingContext.GLOBAL TC) with CALLABLE := callableTypeDefEnv_update } : globalTypingLayer) } : typingContext); (.pure ((TC' : typingContext))))))))))))))))))))))))))))))))


noncomputable def «$add_callableDef_non_overload_t:clause:1» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.callableId) (input3 : SpecTec.callableTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let callableId : SpecTec.callableId := input2; (let callableTypeDefIR : SpecTec.callableTypeDefIR := input3; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (let callableTypeDefEnv : SpecTec.callableTypeDefEnv := (blockTypingLayer.CALLABLE (typingContext.BLOCK TC)); (match callableId with | .«% `( % `)» «exec:1» «exec:2» => (let nameIR : SpecTec.nameIR := «exec:1»; (let «_id*» : (_root_.List id) := «exec:2»; (.bind (.call ⟨(set SpecTec.callableId), SpecTecCall.«$dom_map» SpecTec.callableId SpecTec.callableTypeDefIR callableTypeDefEnv⟩) (fun («exec:3» : (set SpecTec.callableId)) => (let «eval:0» : (set SpecTec.callableId) := «exec:3»; (match «eval:0» with | .«`{ % `}» «exec:4» => (let «eval:2» : (_root_.List SpecTec.callableId) := «exec:4»; (.bind (.call ⟨((_root_.List (_root_.List id)) × (_root_.List SpecTec.nameIR)), SpecTecCall.«$add_callableDef_non_overload_t:case_2:pattern-iter:1» «eval:2»⟩) (fun («exec:5» : ((_root_.List (_root_.List id)) × (_root_.List SpecTec.nameIR))) => (let «_id'**» : (_root_.List (_root_.List id)) := («exec:5»).1; (let «nameIR_k*» : (_root_.List SpecTec.nameIR) := («exec:5»).2; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$in_set» SpecTec.nameIR nameIR ((set.«`{ % `}» «nameIR_k*») : (set SpecTec.nameIR))⟩) (fun («exec:6» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:6»; (.bind (.guard ((¬ («eval:3» = true)))) (fun (_ : Unit) => (.bind (.call ⟨(map SpecTec.callableId SpecTec.callableTypeDefIR), SpecTecCall.«$add_map» SpecTec.callableId SpecTec.callableTypeDefIR callableTypeDefEnv callableId callableTypeDefIR⟩) (fun («exec:7» : (map SpecTec.callableId SpecTec.callableTypeDefIR)) => (let «eval:4» : (map SpecTec.callableId SpecTec.callableTypeDefIR) := «exec:7»; (let callableTypeDefEnv_update : SpecTec.callableTypeDefEnv := «eval:4»; (let TC' : typingContext := ({ TC with BLOCK := ({ (typingContext.BLOCK TC) with CALLABLE := callableTypeDefEnv_update } : blockTypingLayer) } : typingContext); (.pure ((TC' : typingContext))))))))))))))))))))))))))))))))


noncomputable def «$add_callableDef_non_overload_t_clauses» (input0 : cursor) (input1 : typingContext) (input2 : callableId) (input3 : callableTypeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_callableDef_non_overload_t:clause:0»  input0 input1 input2 input3), fun (_ : _root_.Unit) => («$add_callableDef_non_overload_t:clause:1»  input0 input1 input2 input3)]


noncomputable def «$add_typeDef_i:clause:0» (input0 : cursor) (input1 : instContext) (input2 : SpecTec.typeId) (input3 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let IC : instContext := input1; (let typeId : SpecTec.typeId := input2; (let typeDefIR : SpecTec.typeDefIR := input3; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (.bind (.call ⟨(map SpecTec.typeId SpecTec.typeDefIR), SpecTecCall.«$add_map» SpecTec.typeId SpecTec.typeDefIR (globalInstLayer.TYPE (instContext.GLOBAL IC)) typeId typeDefIR⟩) (fun («exec:1» : (map SpecTec.typeId SpecTec.typeDefIR)) => (let «eval:0» : (map SpecTec.typeId SpecTec.typeDefIR) := «exec:1»; (let typeDefEnv : SpecTec.typeDefEnv := «eval:0»; (.pure ((({ IC with GLOBAL := ({ (instContext.GLOBAL IC) with TYPE := typeDefEnv } : globalInstLayer) } : instContext) : instContext)))))))))))))


noncomputable def «$add_typeDef_i_clauses» (input0 : cursor) (input1 : instContext) (input2 : typeId) (input3 : typeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_typeDef_i:clause:0»  input0 input1 input2 input3)]


noncomputable def «$add_callableDef_overload_i:clause:0» (input0 : cursor) (input1 : instContext) (input2 : SpecTec.callableId) (input3 : SpecTec.callableDef) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let IC : instContext := input1; (let callableId : SpecTec.callableId := input2; (let callableDef : SpecTec.callableDef := input3; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (.bind (.call ⟨(set SpecTec.callableId), SpecTecCall.«$dom_map» SpecTec.callableId SpecTec.callableDef (globalInstLayer.CALLABLE (instContext.GLOBAL IC))⟩) (fun («exec:1» : (set SpecTec.callableId)) => (let «eval:0» : (set SpecTec.callableId) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$in_set» SpecTec.callableId callableId «eval:0»⟩) (fun («exec:2» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:2»; (.bind (.guard ((¬ («eval:1» = true)))) (fun (_ : Unit) => (.bind (.call ⟨(map SpecTec.callableId SpecTec.callableDef), SpecTecCall.«$add_map» SpecTec.callableId SpecTec.callableDef (globalInstLayer.CALLABLE (instContext.GLOBAL IC)) callableId callableDef⟩) (fun («exec:3» : (map SpecTec.callableId SpecTec.callableDef)) => (let «eval:2» : (map SpecTec.callableId SpecTec.callableDef) := «exec:3»; (let callableDefEnv : SpecTec.callableDefEnv := «eval:2»; (.pure ((({ IC with GLOBAL := ({ (instContext.GLOBAL IC) with CALLABLE := callableDefEnv } : globalInstLayer) } : instContext) : instContext)))))))))))))))))))))


noncomputable def «$add_callableDef_overload_i:clause:1» (input0 : cursor) (input1 : instContext) (input2 : SpecTec.callableId) (input3 : SpecTec.callableDef) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let IC : instContext := input1; (let callableId : SpecTec.callableId := input2; (let callableDef : SpecTec.callableDef := input3; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (.bind (.call ⟨(set SpecTec.callableId), SpecTecCall.«$dom_map» SpecTec.callableId SpecTec.callableDef (blockInstLayer.CALLABLE (instContext.BLOCK IC))⟩) (fun («exec:1» : (set SpecTec.callableId)) => (let «eval:0» : (set SpecTec.callableId) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$in_set» SpecTec.callableId callableId «eval:0»⟩) (fun («exec:2» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:2»; (.bind (.guard ((¬ («eval:1» = true)))) (fun (_ : Unit) => (.bind (.call ⟨(map SpecTec.callableId SpecTec.callableDef), SpecTecCall.«$add_map» SpecTec.callableId SpecTec.callableDef (blockInstLayer.CALLABLE (instContext.BLOCK IC)) callableId callableDef⟩) (fun («exec:3» : (map SpecTec.callableId SpecTec.callableDef)) => (let «eval:2» : (map SpecTec.callableId SpecTec.callableDef) := «exec:3»; (let callableDefEnv : SpecTec.callableDefEnv := «eval:2»; (.pure ((({ IC with BLOCK := ({ (instContext.BLOCK IC) with CALLABLE := callableDefEnv } : blockInstLayer) } : instContext) : instContext)))))))))))))))))))))


noncomputable def «$add_callableDef_overload_i_clauses» (input0 : cursor) (input1 : instContext) (input2 : callableId) (input3 : callableDef) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_callableDef_overload_i:clause:0»  input0 input1 input2 input3), fun (_ : _root_.Unit) => («$add_callableDef_overload_i:clause:1»  input0 input1 input2 input3)]

end SpecTec
