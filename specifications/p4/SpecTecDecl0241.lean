import SpecTecDecl0240

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$add_callableDef_non_overload_i:clause:0» (input0 : cursor) (input1 : instContext) (input2 : SpecTec.callableId) (input3 : SpecTec.callableDef) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let IC : instContext := input1; (let callableId : SpecTec.callableId := input2; (let callableDef : SpecTec.callableDef := input3; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (match callableId with | .«% `( % `)» «exec:1» «exec:2» => (let id : SpecTec.id := «exec:1»; (let «_id*» : (_root_.List SpecTec.id) := «exec:2»; (.bind (.call ⟨(set SpecTec.callableId), SpecTecCall.«$dom_map» SpecTec.callableId SpecTec.callableDef (globalInstLayer.CALLABLE (instContext.GLOBAL IC))⟩) (fun («exec:3» : (set SpecTec.callableId)) => (let «eval:0» : (set SpecTec.callableId) := «exec:3»; (match «eval:0» with | .«`{ % `}» «exec:4» => (let «eval:2» : (_root_.List SpecTec.callableId) := «exec:4»; (.bind (.call ⟨((_root_.List (_root_.List SpecTec.id)) × (_root_.List SpecTec.id)), SpecTecCall.«$add_callableDef_non_overload_i:case_1:pattern-iter:1» «eval:2»⟩) (fun («exec:5» : ((_root_.List (_root_.List SpecTec.id)) × (_root_.List SpecTec.id))) => (let «_id'**» : (_root_.List (_root_.List SpecTec.id)) := («exec:5»).1; (let «id_k*» : (_root_.List SpecTec.id) := («exec:5»).2; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$in_set» SpecTec.id id ((set.«`{ % `}» «id_k*») : (set SpecTec.id))⟩) (fun («exec:6» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:6»; (.bind (.guard ((¬ («eval:3» = true)))) (fun (_ : Unit) => (.bind (.call ⟨(map SpecTec.callableId SpecTec.callableDef), SpecTecCall.«$add_map» SpecTec.callableId SpecTec.callableDef (globalInstLayer.CALLABLE (instContext.GLOBAL IC)) callableId callableDef⟩) (fun («exec:7» : (map SpecTec.callableId SpecTec.callableDef)) => (let «eval:4» : (map SpecTec.callableId SpecTec.callableDef) := «exec:7»; (let callableDefEnv : SpecTec.callableDefEnv := «eval:4»; (.pure ((({ IC with GLOBAL := ({ (instContext.GLOBAL IC) with CALLABLE := callableDefEnv } : globalInstLayer) } : instContext) : instContext))))))))))))))))))))))))))))))


noncomputable def «$add_callableDef_non_overload_i:clause:1» (input0 : cursor) (input1 : instContext) (input2 : SpecTec.callableId) (input3 : SpecTec.callableDef) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let IC : instContext := input1; (let callableId : SpecTec.callableId := input2; (let callableDef : SpecTec.callableDef := input3; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (match callableId with | .«% `( % `)» «exec:1» «exec:2» => (let id : SpecTec.id := «exec:1»; (let «_id*» : (_root_.List SpecTec.id) := «exec:2»; (.bind (.call ⟨(set SpecTec.callableId), SpecTecCall.«$dom_map» SpecTec.callableId SpecTec.callableDef (blockInstLayer.CALLABLE (instContext.BLOCK IC))⟩) (fun («exec:3» : (set SpecTec.callableId)) => (let «eval:0» : (set SpecTec.callableId) := «exec:3»; (match «eval:0» with | .«`{ % `}» «exec:4» => (let «eval:2» : (_root_.List SpecTec.callableId) := «exec:4»; (.bind (.call ⟨((_root_.List (_root_.List SpecTec.id)) × (_root_.List SpecTec.id)), SpecTecCall.«$add_callableDef_non_overload_i:case_2:pattern-iter:1» «eval:2»⟩) (fun («exec:5» : ((_root_.List (_root_.List SpecTec.id)) × (_root_.List SpecTec.id))) => (let «_id'**» : (_root_.List (_root_.List SpecTec.id)) := («exec:5»).1; (let «id_k*» : (_root_.List SpecTec.id) := («exec:5»).2; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$in_set» SpecTec.id id ((set.«`{ % `}» «id_k*») : (set SpecTec.id))⟩) (fun («exec:6» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:6»; (.bind (.guard ((¬ («eval:3» = true)))) (fun (_ : Unit) => (.bind (.call ⟨(map SpecTec.callableId SpecTec.callableDef), SpecTecCall.«$add_map» SpecTec.callableId SpecTec.callableDef (blockInstLayer.CALLABLE (instContext.BLOCK IC)) callableId callableDef⟩) (fun («exec:7» : (map SpecTec.callableId SpecTec.callableDef)) => (let «eval:4» : (map SpecTec.callableId SpecTec.callableDef) := «exec:7»; (let callableDefEnv : SpecTec.callableDefEnv := «eval:4»; (.pure ((({ IC with BLOCK := ({ (instContext.BLOCK IC) with CALLABLE := callableDefEnv } : blockInstLayer) } : instContext) : instContext))))))))))))))))))))))))))))))


noncomputable def «$add_callableDef_non_overload_i_clauses» (input0 : cursor) (input1 : instContext) (input2 : callableId) (input3 : callableDef) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_callableDef_non_overload_i:clause:0»  input0 input1 input2 input3), fun (_ : _root_.Unit) => («$add_callableDef_non_overload_i:clause:1»  input0 input1 input2 input3)]


noncomputable def «FuncDecl_inst:clause:0» (input0 : cursor) (input1 : instContext) (input2 : functionDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let IC_0 : instContext := input1; (match input2 with | .«% % %» «exec:1» «exec:2» «exec:3» => (let annotationList : SpecTec.annotationList := «exec:1»; (match «exec:2» with | .«% % `< % ',' % `> `( % `)» «exec:4» «exec:5» «exec:6» «exec:7» «exec:8» => (let typeIR : SpecTec.typeIR := «exec:4»; (let nameIR : SpecTec.nameIR := «exec:5»; (let typeParameterListIR_expl : SpecTec.typeParameterListIR := «exec:6»; (let typeParameterListIR_impl : SpecTec.typeParameterListIR := «exec:7»; (let parameterListIR : SpecTec.parameterListIR := «exec:8»; (let blockStatementIR : SpecTec.blockStatementIR := «exec:3»; (.bind (.call ⟨SpecTec.callableId, SpecTecCall.«$callableId_IR» nameIR parameterListIR⟩) (fun («exec:9» : SpecTec.callableId) => (let «eval:0» : SpecTec.callableId := «exec:9»; (let callableId : SpecTec.callableId := «eval:0»; (let typeParameterListIR : SpecTec.typeParameterListIR := (typeParameterListIR_expl ++ typeParameterListIR_impl); (let definedFunctionDef : SpecTec.definedFunctionDef := ((SpecTec.definedFunctionDef.«FUNCTION % `< % `> `( % `) %» nameIR typeParameterListIR parameterListIR blockStatementIR) : SpecTec.definedFunctionDef); (.bind (.call ⟨instContext, SpecTecCall.«$add_callableDef_overload_i» p IC_0 callableId («cast:definedFunctionDef:callableDef» definedFunctionDef)⟩) (fun («exec:10» : instContext) => (let «eval:1» : instContext := «exec:10»; (let IC_1 : instContext := «eval:1»; (.pure ((IC_1 : instContext))))))))))))))))))))))))


noncomputable def FuncDecl_inst_clauses (input0 : cursor) (input1 : instContext) (input2 : functionDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («FuncDecl_inst:clause:0»  input0 input1 input2)]


noncomputable def «ActionDecl_inst:clause:0» (input0 : cursor) (input1 : instContext) (input2 : actionDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let IC_0 : instContext := input1; (match input2 with | .«% ACTION % `( % `) %» «exec:1» «exec:2» «exec:3» «exec:4» => (let annotationList : SpecTec.annotationList := «exec:1»; (let nameIR : SpecTec.nameIR := «exec:2»; (let parameterListIR : SpecTec.parameterListIR := «exec:3»; (let blockStatementIR : SpecTec.blockStatementIR := «exec:4»; (.bind (.call ⟨SpecTec.callableId, SpecTecCall.«$callableId_IR» nameIR parameterListIR⟩) (fun («exec:5» : SpecTec.callableId) => (let «eval:0» : SpecTec.callableId := «exec:5»; (let callableId : SpecTec.callableId := «eval:0»; (let actionDef : SpecTec.actionDef := ((SpecTec.actionDef.«% ACTION % `( % `) %» annotationList nameIR parameterListIR blockStatementIR) : SpecTec.actionDef); (.bind (.call ⟨instContext, SpecTecCall.«$add_callableDef_non_overload_i» p IC_0 callableId («cast:actionDef:callableDef» actionDef)⟩) (fun («exec:6» : instContext) => (let «eval:1» : instContext := «exec:6»; (let IC_1 : instContext := «eval:1»; (.pure ((IC_1 : instContext)))))))))))))))))))


noncomputable def ActionDecl_inst_clauses (input0 : cursor) (input1 : instContext) (input2 : actionDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («ActionDecl_inst:clause:0»  input0 input1 input2)]


noncomputable def «$bound:clause:0» (input0 : cursor) (input1 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (.pure ((((set.«`{ % `}» ([] : (_root_.List typeId))) : (set typeId)) : bound)))))))


noncomputable def «$bound:clause:1» (input0 : cursor) (input1 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (.bind (.call ⟨(set typeId), SpecTecCall.«$dom_map» typeId typeDefIR (blockTypingLayer.TYPE (typingContext.BLOCK TC))⟩) (fun («exec:1» : (set typeId)) => (let «eval:0» : (set typeId) := «exec:1»; (.pure ((«eval:0» : bound))))))))))


noncomputable def «$bound:clause:2» (input0 : cursor) (input1 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (.bind (.call ⟨bound, SpecTecCall.«$bound» ((cursor.BLOCK) : cursor) TC⟩) (fun («exec:1» : bound) => (let «eval:0» : bound := «exec:1»; (let B_block : bound := «eval:0»; (.bind (.call ⟨(set typeId), SpecTecCall.«$dom_map» typeId typeDefIR (localTypingLayer.TYPE (typingContext.LOCAL TC))⟩) (fun («exec:2» : (set typeId)) => (let «eval:1» : (set typeId) := «exec:2»; (let B_local : bound := «eval:1»; (.pure (((«$union_set» B_block B_local) : bound)))))))))))))))


noncomputable def «$bound_clauses» (input0 : cursor) (input1 : typingContext) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$bound:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$bound:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$bound:clause:2»  input0 input1)]


noncomputable def «$add_typeDef_t:clause:0» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.typeId) (input3 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let typeId : SpecTec.typeId := input2; (let typeDefIR : SpecTec.typeDefIR := input3; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (let typeDefEnv : SpecTec.typeDefEnv := (globalTypingLayer.TYPE (typingContext.GLOBAL TC)); (.bind (.call ⟨(set SpecTec.typeId), SpecTecCall.«$dom_map» SpecTec.typeId SpecTec.typeDefIR typeDefEnv⟩) (fun («exec:1» : (set SpecTec.typeId)) => (let «eval:0» : (set SpecTec.typeId) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$in_set» SpecTec.typeId typeId «eval:0»⟩) (fun («exec:2» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:2»; (.bind (.guard ((¬ («eval:1» = true)))) (fun (_ : Unit) => (.bind (.call ⟨(map SpecTec.typeId SpecTec.typeDefIR), SpecTecCall.«$add_map» SpecTec.typeId SpecTec.typeDefIR typeDefEnv typeId typeDefIR⟩) (fun («exec:3» : (map SpecTec.typeId SpecTec.typeDefIR)) => (let «eval:2» : (map SpecTec.typeId SpecTec.typeDefIR) := «exec:3»; (let typeDefEnv_update : SpecTec.typeDefEnv := «eval:2»; (let TC' : typingContext := ({ TC with GLOBAL := ({ (typingContext.GLOBAL TC) with TYPE := typeDefEnv_update } : globalTypingLayer) } : typingContext); (.pure ((TC' : typingContext)))))))))))))))))))))))


noncomputable def «$add_typeDef_t:clause:1» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.typeId) (input3 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let typeId : SpecTec.typeId := input2; (let typeDefIR : SpecTec.typeDefIR := input3; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (let typeDefEnv : SpecTec.typeDefEnv := (blockTypingLayer.TYPE (typingContext.BLOCK TC)); (.bind (.call ⟨(set SpecTec.typeId), SpecTecCall.«$dom_map» SpecTec.typeId SpecTec.typeDefIR typeDefEnv⟩) (fun («exec:1» : (set SpecTec.typeId)) => (let «eval:0» : (set SpecTec.typeId) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$in_set» SpecTec.typeId typeId «eval:0»⟩) (fun («exec:2» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:2»; (.bind (.guard ((¬ («eval:1» = true)))) (fun (_ : Unit) => (.bind (.call ⟨(map SpecTec.typeId SpecTec.typeDefIR), SpecTecCall.«$add_map» SpecTec.typeId SpecTec.typeDefIR typeDefEnv typeId typeDefIR⟩) (fun («exec:3» : (map SpecTec.typeId SpecTec.typeDefIR)) => (let «eval:2» : (map SpecTec.typeId SpecTec.typeDefIR) := «exec:3»; (let typeDefEnv_update : SpecTec.typeDefEnv := «eval:2»; (let TC' : typingContext := ({ TC with BLOCK := ({ (typingContext.BLOCK TC) with TYPE := typeDefEnv_update } : blockTypingLayer) } : typingContext); (.pure ((TC' : typingContext)))))))))))))))))))))))


noncomputable def «$add_typeDef_t:clause:2» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.typeId) (input3 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let typeId : SpecTec.typeId := input2; (let typeDefIR : SpecTec.typeDefIR := input3; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (let typeDefEnv : SpecTec.typeDefEnv := (localTypingLayer.TYPE (typingContext.LOCAL TC)); (.bind (.call ⟨(set SpecTec.typeId), SpecTecCall.«$dom_map» SpecTec.typeId SpecTec.typeDefIR typeDefEnv⟩) (fun («exec:1» : (set SpecTec.typeId)) => (let «eval:0» : (set SpecTec.typeId) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$in_set» SpecTec.typeId typeId «eval:0»⟩) (fun («exec:2» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:2»; (.bind (.guard ((¬ («eval:1» = true)))) (fun (_ : Unit) => (.bind (.call ⟨(map SpecTec.typeId SpecTec.typeDefIR), SpecTecCall.«$add_map» SpecTec.typeId SpecTec.typeDefIR typeDefEnv typeId typeDefIR⟩) (fun («exec:3» : (map SpecTec.typeId SpecTec.typeDefIR)) => (let «eval:2» : (map SpecTec.typeId SpecTec.typeDefIR) := «exec:3»; (let typeDefEnv_update : SpecTec.typeDefEnv := «eval:2»; (let TC' : typingContext := ({ TC with LOCAL := ({ (typingContext.LOCAL TC) with TYPE := typeDefEnv_update } : localTypingLayer) } : typingContext); (.pure ((TC' : typingContext)))))))))))))))))))))))


noncomputable def «$add_typeDef_t_clauses» (input0 : cursor) (input1 : typingContext) (input2 : typeId) (input3 : typeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_typeDef_t:clause:0»  input0 input1 input2 input3), fun (_ : _root_.Unit) => («$add_typeDef_t:clause:1»  input0 input1 input2 input3), fun (_ : _root_.Unit) => («$add_typeDef_t:clause:2»  input0 input1 input2 input3)]


noncomputable def «$add_typeDefs_t:clause:0» (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List typeId)) (input3 : (_root_.List typeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let «typeId*» : (_root_.List typeId) := input2; (let «typeDefIR*» : (_root_.List typeDefIR) := input3; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeId*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeDefIR*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((TC : typingContext)))))))))))


noncomputable def «$add_typeDefs_t:clause:1» (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List typeId)) (input3 : (_root_.List typeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let «typeId*» : (_root_.List typeId) := input2; (let «typeDefIR*» : (_root_.List typeDefIR) := input3; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeId*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «typeId*» with | «exec:2» :: «exec:1» => (let typeId_h : typeId := «exec:2»; (let «typeId_t*» : (_root_.List typeId) := «exec:1»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeDefIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «typeDefIR*» with | «exec:4» :: «exec:3» => (let typeDefIR_h : typeDefIR := «exec:4»; (let «typeDefIR_t*» : (_root_.List typeDefIR) := «exec:3»; (.bind (.call ⟨typingContext, SpecTecCall.«$add_typeDef_t» p TC typeId_h typeDefIR_h⟩) (fun («exec:5» : typingContext) => (let «eval:0» : typingContext := «exec:5»; (let TC' : typingContext := «eval:0»; (.bind (.call ⟨typingContext, SpecTecCall.«$add_typeDefs_t» p TC' «typeId_t*» «typeDefIR_t*»⟩) (fun («exec:6» : typingContext) => (let «eval:1» : typingContext := «exec:6»; (let TC'' : typingContext := «eval:1»; (.pure ((TC'' : typingContext))))))))))))) | [] => .unmatch))))) | [] => .unmatch)))))))


noncomputable def «$add_typeDefs_t_clauses» (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List typeId)) (input3 : (_root_.List typeDefIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_typeDefs_t:clause:0»  input0 input1 input2 input3), fun (_ : _root_.Unit) => («$add_typeDefs_t:clause:1»  input0 input1 input2 input3)]


noncomputable def «$add_typeParameters_t:clause:0» (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let «typeId*» : (_root_.List typeId) := input2; (.bind (.call ⟨(_root_.List typeDefIR), SpecTecCall.«$add_typeParameters_t:case_1:iter:0» «typeId*»⟩) (fun («exec:1» : (_root_.List typeDefIR)) => (let «eval:1» : (_root_.List typeDefIR) := «exec:1»; (.bind (.call ⟨typingContext, SpecTecCall.«$add_typeDefs_t» p TC «typeId*» «eval:1»⟩) (fun («exec:2» : typingContext) => (let «eval:2» : typingContext := «exec:2»; (.pure ((«eval:2» : typingContext))))))))))))


noncomputable def «$add_typeParameters_t_clauses» (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_typeParameters_t:clause:0»  input0 input1 input2)]


noncomputable def «$instantiable_extern:clause:0» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.instctxt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let instctxt : SpecTec.instctxt := input2; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))))


noncomputable def «$instantiable_extern:clause:1» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.instctxt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let instctxt : SpecTec.instctxt := input2; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))))


noncomputable def «$instantiable_extern:clause:2» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.instctxt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let instctxt : SpecTec.instctxt := input2; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))))


noncomputable def «$instantiable_extern_clauses» (input0 : cursor) (input1 : typingContext) (input2 : instctxt) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$instantiable_extern:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$instantiable_extern:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$instantiable_extern:clause:2»  input0 input1 input2)]


noncomputable def «$instantiable_parser:clause:0» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.instctxt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let instctxt : SpecTec.instctxt := input2; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (.pure (((_root_.Decidable.decide (instctxt = ((SpecTec.instctxt.ANON) : SpecTec.instctxt))) : _root_.Bool))))))))


noncomputable def «$instantiable_parser:clause:1» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.instctxt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let instctxt : SpecTec.instctxt := input2; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (let blockKind : SpecTec.blockKind := (blockTypingLayer.KIND (typingContext.BLOCK TC)); (.pure ((((_root_.Decidable.decide (blockKind = ((SpecTec.blockKind.PARSER) : SpecTec.blockKind))) || (_root_.Decidable.decide (blockKind = ((SpecTec.blockKind.PACKAGE) : SpecTec.blockKind)))) : _root_.Bool)))))))))


noncomputable def «$instantiable_parser:clause:2» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.instctxt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let instctxt : SpecTec.instctxt := input2; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (let localKind : SpecTec.localKind := (localTypingLayer.KIND (typingContext.LOCAL TC)); (.pure (((_root_.Decidable.decide (localKind = ((SpecTec.localKind.PARSER_STATE) : SpecTec.localKind))) : _root_.Bool)))))))))


noncomputable def «$instantiable_parser_clauses» (input0 : cursor) (input1 : typingContext) (input2 : instctxt) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$instantiable_parser:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$instantiable_parser:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$instantiable_parser:clause:2»  input0 input1 input2)]


noncomputable def «$instantiable_control:clause:0» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.instctxt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let instctxt : SpecTec.instctxt := input2; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (.pure (((_root_.Decidable.decide (instctxt = ((SpecTec.instctxt.ANON) : SpecTec.instctxt))) : _root_.Bool))))))))


noncomputable def «$instantiable_control:clause:1» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.instctxt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let instctxt : SpecTec.instctxt := input2; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (let blockKind : SpecTec.blockKind := (blockTypingLayer.KIND (typingContext.BLOCK TC)); (.pure ((((_root_.Decidable.decide (blockKind = ((SpecTec.blockKind.CONTROL) : SpecTec.blockKind))) || (_root_.Decidable.decide (blockKind = ((SpecTec.blockKind.PACKAGE) : SpecTec.blockKind)))) : _root_.Bool)))))))))


noncomputable def «$instantiable_control:clause:2» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.instctxt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let instctxt : SpecTec.instctxt := input2; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (let localKind : SpecTec.localKind := (localTypingLayer.KIND (typingContext.LOCAL TC)); (.pure (((_root_.Decidable.decide (localKind = ((SpecTec.localKind.CONTROL_APPLY_METHOD) : SpecTec.localKind))) : _root_.Bool)))))))))


noncomputable def «$instantiable_control_clauses» (input0 : cursor) (input1 : typingContext) (input2 : instctxt) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$instantiable_control:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$instantiable_control:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$instantiable_control:clause:2»  input0 input1 input2)]

end SpecTec
