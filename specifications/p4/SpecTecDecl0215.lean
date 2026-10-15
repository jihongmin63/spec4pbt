import SpecTecDecl0214

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$parameterListIR_of_controlApplyMethodDef:clause:0» (input0 : controlApplyMethodDef) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«CONTROL_APPLY `( % `) `{ % ';' % ';' % `}» «exec:1» «exec:2» «exec:3» «exec:4» => (let parameterListIR : SpecTec.parameterListIR := «exec:1»; (let _controlLocalDeclarationListIR : controlLocalDeclarationListIR := «exec:2»; (let _actionDefEnv : actionDefEnv := «exec:3»; (let _controlBodyIR : controlBodyIR := «exec:4»; (.pure ((parameterListIR : (_root_.List parameterIR)))))))))


noncomputable def «$parameterListIR_of_controlApplyMethodDef_clauses» (input0 : controlApplyMethodDef) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$parameterListIR_of_controlApplyMethodDef:clause:0»  input0)]


noncomputable def «$empty_frame:clause:0»  : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (.bind (.call ⟨(map id value), SpecTecCall.«$empty_map» id value⟩) (fun («exec:1» : (map id value)) => (let «eval:0» : (map id value) := «exec:1»; (.pure ((«eval:0» : frame))))))


noncomputable def «$empty_frame_clauses» : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$empty_frame:clause:0»  )]


noncomputable def «$parameterListIR_of_parserApplyMethodDef:clause:0» (input0 : parserApplyMethodDef) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«PARSER_APPLY `( % `) `{ % ';' % `}» «exec:1» «exec:2» «exec:3» => (let parameterListIR : SpecTec.parameterListIR := «exec:1»; (let _parserLocalDeclarationListIR : parserLocalDeclarationListIR := «exec:2»; (let _stateEnv : stateEnv := «exec:3»; (.pure ((parameterListIR : (_root_.List parameterIR))))))))


noncomputable def «$parameterListIR_of_parserApplyMethodDef_clauses» (input0 : parserApplyMethodDef) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$parameterListIR_of_parserApplyMethodDef:clause:0»  input0)]


noncomputable def «$empty_stateEnv:clause:0»  : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (.bind (.call ⟨(map id parserStateIR), SpecTecCall.«$empty_map» id parserStateIR⟩) (fun («exec:1» : (map id parserStateIR)) => (let «eval:0» : (map id parserStateIR) := «exec:1»; (.pure ((«eval:0» : stateEnv))))))


noncomputable def «$empty_stateEnv_clauses» : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$empty_stateEnv:clause:0»  )]


noncomputable def «$empty_callableDefEnv:clause:0»  : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (.bind (.call ⟨(map callableId callableDef), SpecTecCall.«$empty_map» callableId callableDef⟩) (fun («exec:1» : (map callableId callableDef)) => (let «eval:0» : (map callableId callableDef) := «exec:1»; (.pure ((«eval:0» : callableDefEnv))))))


noncomputable def «$empty_callableDefEnv_clauses» : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$empty_callableDefEnv:clause:0»  )]


noncomputable def «$empty_constructorDefEnv:clause:0»  : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (.bind (.call ⟨(map callableId constructorDef), SpecTecCall.«$empty_map» callableId constructorDef⟩) (fun («exec:1» : (map callableId constructorDef)) => (let «eval:0» : (map callableId constructorDef) := «exec:1»; (.pure ((«eval:0» : constructorDefEnv))))))


noncomputable def «$empty_constructorDefEnv_clauses» : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$empty_constructorDefEnv:clause:0»  )]


noncomputable def «$empty_store:clause:0»  : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (.bind (.call ⟨(map objectId object), SpecTecCall.«$empty_map» objectId object⟩) (fun («exec:1» : (map objectId object)) => (let «eval:0» : (map objectId object) := «exec:1»; (let store : SpecTec.store := «eval:0»; (.pure ((store : SpecTec.store)))))))


noncomputable def «$empty_store_clauses» : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$empty_store:clause:0»  )]


noncomputable def «$add_store:clause:0» (input0 : SpecTec.store) (input1 : SpecTec.objectId) (input2 : SpecTec.object) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let store : SpecTec.store := input0; (let objectId : SpecTec.objectId := input1; (let object : SpecTec.object := input2; (.bind (.call ⟨(map SpecTec.objectId SpecTec.object), SpecTecCall.«$add_map» SpecTec.objectId SpecTec.object store objectId object⟩) (fun («exec:1» : (map SpecTec.objectId SpecTec.object)) => (let «eval:0» : (map SpecTec.objectId SpecTec.object) := «exec:1»; (let store' : SpecTec.store := «eval:0»; (.pure ((store' : SpecTec.store))))))))))


noncomputable def «$add_store_clauses» (input0 : store) (input1 : objectId) (input2 : object) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_store:clause:0»  input0 input1 input2)]


noncomputable def «$find_store:clause:0» (input0 : SpecTec.store) (input1 : SpecTec.objectId) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let store : SpecTec.store := input0; (let objectId : SpecTec.objectId := input1; (.bind (.call ⟨(_root_.Option SpecTec.object), SpecTecCall.«$find_map» SpecTec.objectId SpecTec.object store objectId⟩) (fun («exec:1» : (_root_.Option SpecTec.object)) => (let «eval:0» : (_root_.Option SpecTec.object) := «exec:1»; (let object'? : (_root_.Option SpecTec.object) := «eval:0»; (.bind (.guard (((_root_.Option.isSome object'?) = true))) (fun (_ : Unit) => (match object'? with | some «exec:2» => (let object : SpecTec.object := «exec:2»; (.pure ((object : SpecTec.object)))) | none => .unmatch)))))))))


noncomputable def «$find_store_clauses» (input0 : store) (input1 : objectId) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_store:clause:0»  input0 input1)]


noncomputable def «$empty_instContext:clause:0»  : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (.bind (.call ⟨constructorDefEnv, SpecTecCall.«$empty_constructorDefEnv»⟩) (fun («exec:1» : constructorDefEnv) => (let «eval:0» : constructorDefEnv := «exec:1»; (.bind (.call ⟨typeDefEnv, SpecTecCall.«$empty_typeDefEnv»⟩) (fun («exec:2» : typeDefEnv) => (let «eval:1» : typeDefEnv := «exec:2»; (.bind (.call ⟨callableDefEnv, SpecTecCall.«$empty_callableDefEnv»⟩) (fun («exec:3» : callableDefEnv) => (let «eval:2» : callableDefEnv := «exec:3»; (.bind (.call ⟨frame, SpecTecCall.«$empty_frame»⟩) (fun («exec:4» : frame) => (let «eval:3» : frame := «exec:4»; (let globalInstLayer : SpecTec.globalInstLayer := ({ CONSTRUCTOR := «eval:0», TYPE := «eval:1», CALLABLE := «eval:2», FRAME := «eval:3» } : SpecTec.globalInstLayer); (.bind (.call ⟨theta, SpecTecCall.«$empty_theta»⟩) (fun («exec:5» : theta) => (let «eval:4» : theta := «exec:5»; (.bind (.call ⟨callableDefEnv, SpecTecCall.«$empty_callableDefEnv»⟩) (fun («exec:6» : callableDefEnv) => (let «eval:5» : callableDefEnv := «exec:6»; (.bind (.call ⟨stateEnv, SpecTecCall.«$empty_stateEnv»⟩) (fun («exec:7» : stateEnv) => (let «eval:6» : stateEnv := «exec:7»; (.bind (.call ⟨frame, SpecTecCall.«$empty_frame»⟩) (fun («exec:8» : frame) => (let «eval:7» : frame := «exec:8»; (let blockInstLayer : SpecTec.blockInstLayer := ({ TYPE := «eval:4», CALLABLE := «eval:5», STATE := «eval:6», FRAME := «eval:7» } : SpecTec.blockInstLayer); (.bind (.call ⟨theta, SpecTecCall.«$empty_theta»⟩) (fun («exec:9» : theta) => (let «eval:8» : theta := «exec:9»; (.bind (.call ⟨frame, SpecTecCall.«$empty_frame»⟩) (fun («exec:10» : frame) => (let «eval:9» : frame := «exec:10»; (let localInstLayer : SpecTec.localInstLayer := ({ TYPE := «eval:8», FRAMES := ([«eval:9»] : (_root_.List frame)) } : SpecTec.localInstLayer); (let IC : instContext := ({ PATH := ([] : (_root_.List nameIR)), GLOBAL := globalInstLayer, BLOCK := blockInstLayer, LOCAL := localInstLayer } : instContext); (.pure ((IC : instContext)))))))))))))))))))))))))))))))))))))


noncomputable def «$empty_instContext_clauses» : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$empty_instContext:clause:0»  )]


noncomputable def «$enter_i:clause:0» (input0 : instContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let IC : instContext := input0; (.bind (.call ⟨frame, SpecTecCall.«$empty_frame»⟩) (fun («exec:1» : frame) => (let «eval:0» : frame := «exec:1»; (.pure ((({ IC with LOCAL := ({ (instContext.LOCAL IC) with FRAMES := («eval:0» :: (localInstLayer.FRAMES (instContext.LOCAL IC))) } : localInstLayer) } : instContext) : instContext)))))))


noncomputable def «$enter_i_clauses» (input0 : instContext) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$enter_i:clause:0»  input0)]


noncomputable def «$exit_i:clause:0» (input0 : instContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let IC : instContext := input0; (let «frame*» : (_root_.List frame) := (localInstLayer.FRAMES (instContext.LOCAL IC)); (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «frame*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «frame*» with | «exec:2» :: «exec:1» => (let frame_h : frame := «exec:2»; (let «frame_t*» : (_root_.List frame) := «exec:1»; (.pure ((({ IC with LOCAL := ({ (instContext.LOCAL IC) with FRAMES := «frame_t*» } : localInstLayer) } : instContext) : instContext))))) | [] => .unmatch)))))


noncomputable def «$exit_i_clauses» (input0 : instContext) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$exit_i:clause:0»  input0)]


noncomputable def «$enter_path_i:clause:0» (input0 : instContext) (input1 : SpecTec.id) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let IC : instContext := input0; (let id : SpecTec.id := input1; (.pure ((({ IC with PATH := ((instContext.PATH IC) ++ ([id] : (_root_.List nameIR))) } : instContext) : instContext)))))


noncomputable def «$enter_path_i_clauses» (input0 : instContext) (input1 : id) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$enter_path_i:clause:0»  input0 input1)]


noncomputable def «$add_parserState_i:clause:0» (input0 : instContext) (input1 : SpecTec.nameIR) (input2 : SpecTec.parserStateIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let IC : instContext := input0; (let nameIR : SpecTec.nameIR := input1; (let parserStateIR : SpecTec.parserStateIR := input2; (.bind (.call ⟨(set SpecTec.nameIR), SpecTecCall.«$dom_map» SpecTec.nameIR SpecTec.parserStateIR (blockInstLayer.STATE (instContext.BLOCK IC))⟩) (fun («exec:1» : (set SpecTec.nameIR)) => (let «eval:0» : (set SpecTec.nameIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$in_set» SpecTec.nameIR nameIR «eval:0»⟩) (fun («exec:2» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:2»; (.bind (.guard ((¬ («eval:1» = true)))) (fun (_ : Unit) => (.bind (.call ⟨(map SpecTec.nameIR SpecTec.parserStateIR), SpecTecCall.«$add_map» SpecTec.nameIR SpecTec.parserStateIR (blockInstLayer.STATE (instContext.BLOCK IC)) nameIR parserStateIR⟩) (fun («exec:3» : (map SpecTec.nameIR SpecTec.parserStateIR)) => (let «eval:2» : (map SpecTec.nameIR SpecTec.parserStateIR) := «exec:3»; (let stateEnv : SpecTec.stateEnv := «eval:2»; (.pure ((({ IC with BLOCK := ({ (instContext.BLOCK IC) with STATE := stateEnv } : blockInstLayer) } : instContext) : instContext))))))))))))))))))


noncomputable def «$add_parserState_i_clauses» (input0 : instContext) (input1 : nameIR) (input2 : parserStateIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_parserState_i:clause:0»  input0 input1 input2)]


noncomputable def «$add_callableDef_non_overload_i:case_1:pattern-iter:1:clause:0» (input0 : (_root_.List callTargetId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List (_root_.List id))), ([] : (_root_.List id))) : ((_root_.List (_root_.List id)) × (_root_.List id))))) | _ :: _ => .unmatch)


noncomputable def «$add_callableDef_non_overload_i:case_1:pattern-iter:1:clause:1» (input0 : (_root_.List callTargetId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% `( % `)» «exec:3» «exec:4» => (let id_k : id := «exec:3»; (let «_id'*» : (_root_.List id) := «exec:4»; (let «pattern-tail:0» : (_root_.List callTargetId) := «exec:1»; (.bind (.call ⟨((_root_.List (_root_.List id)) × (_root_.List id)), SpecTecCall.«$add_callableDef_non_overload_i:case_1:pattern-iter:1» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List (_root_.List id)) × (_root_.List id))) => (let «pattern-tail:1» : (_root_.List (_root_.List id)) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List id) := («exec:5»).2; (.pure ((((«_id'*» :: «pattern-tail:1»), (id_k :: «pattern-tail:2»)) : ((_root_.List (_root_.List id)) × (_root_.List id))))))))))))) | [] => .unmatch)


noncomputable def «$add_callableDef_non_overload_i:case_1:pattern-iter:1_clauses» (input0 : (_root_.List callTargetId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_callableDef_non_overload_i:case_1:pattern-iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$add_callableDef_non_overload_i:case_1:pattern-iter:1:clause:1»  input0)]


noncomputable def «$add_callableDef_non_overload_i:case_2:pattern-iter:1:clause:0» (input0 : (_root_.List callTargetId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List (_root_.List id))), ([] : (_root_.List id))) : ((_root_.List (_root_.List id)) × (_root_.List id))))) | _ :: _ => .unmatch)

end SpecTec
