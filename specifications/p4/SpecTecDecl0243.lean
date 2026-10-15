import SpecTecDecl0242

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$callable_tableApplyMethod:clause:1» (input0 : cursor) (input1 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))


noncomputable def «$callable_tableApplyMethod:clause:2» (input0 : cursor) (input1 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (let localKind : SpecTec.localKind := (localTypingLayer.KIND (typingContext.LOCAL TC)); (.pure ((((_root_.Decidable.decide (localKind = ((SpecTec.localKind.CONTROL_APPLY_METHOD) : SpecTec.localKind))) || (_root_.Decidable.decide (localKind = ((SpecTec.localKind.TABLE_APPLY_METHOD) : SpecTec.localKind)))) : _root_.Bool))))))))


noncomputable def «$callable_tableApplyMethod_clauses» (input0 : cursor) (input1 : typingContext) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$callable_tableApplyMethod:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$callable_tableApplyMethod:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$callable_tableApplyMethod:clause:2»  input0 input1)]


noncomputable def «$inherit_i:clause:0» (input0 : cursor) (input1 : instContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let IC : instContext := input1; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (.bind (.call ⟨theta, SpecTecCall.«$empty_theta»⟩) (fun («exec:1» : theta) => (let «eval:0» : theta := «exec:1»; (.bind (.call ⟨callableDefEnv, SpecTecCall.«$empty_callableDefEnv»⟩) (fun («exec:2» : callableDefEnv) => (let «eval:1» : callableDefEnv := «exec:2»; (.bind (.call ⟨stateEnv, SpecTecCall.«$empty_stateEnv»⟩) (fun («exec:3» : stateEnv) => (let «eval:2» : stateEnv := «exec:3»; (.bind (.call ⟨frame, SpecTecCall.«$empty_frame»⟩) (fun («exec:4» : frame) => (let «eval:3» : frame := «exec:4»; (let blockInstLayer : SpecTec.blockInstLayer := ({ TYPE := «eval:0», CALLABLE := «eval:1», STATE := «eval:2», FRAME := «eval:3» } : SpecTec.blockInstLayer); (.bind (.call ⟨theta, SpecTecCall.«$empty_theta»⟩) (fun («exec:5» : theta) => (let «eval:4» : theta := «exec:5»; (.bind (.call ⟨frame, SpecTecCall.«$empty_frame»⟩) (fun («exec:6» : frame) => (let «eval:5» : frame := «exec:6»; (let localInstLayer : SpecTec.localInstLayer := ({ TYPE := «eval:4», FRAMES := ([«eval:5»] : (_root_.List frame)) } : SpecTec.localInstLayer); (.pure ((({ ({ IC with BLOCK := blockInstLayer } : instContext) with LOCAL := localInstLayer } : instContext) : instContext)))))))))))))))))))))))))))


noncomputable def «$inherit_i:clause:1» (input0 : cursor) (input1 : instContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let IC : instContext := input1; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (.bind (.call ⟨theta, SpecTecCall.«$empty_theta»⟩) (fun («exec:1» : theta) => (let «eval:0» : theta := «exec:1»; (.bind (.call ⟨frame, SpecTecCall.«$empty_frame»⟩) (fun («exec:2» : frame) => (let «eval:1» : frame := «exec:2»; (let localInstLayer : SpecTec.localInstLayer := ({ TYPE := «eval:0», FRAMES := ([«eval:1»] : (_root_.List frame)) } : SpecTec.localInstLayer); (.pure ((({ IC with LOCAL := localInstLayer } : instContext) : instContext))))))))))))))


noncomputable def «$inherit_i:clause:2» (input0 : cursor) (input1 : instContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let IC : instContext := input1; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (.pure ((IC : instContext)))))))


noncomputable def «$inherit_i_clauses» (input0 : cursor) (input1 : instContext) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$inherit_i:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$inherit_i:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$inherit_i:clause:2»  input0 input1)]


noncomputable def «$add_var_i:clause:0» (input0 : cursor) (input1 : instContext) (input2 : SpecTec.id) (input3 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let IC : instContext := input1; (let id : SpecTec.id := input2; (let value : SpecTec.value := input3; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (.bind (.call ⟨(set SpecTec.id), SpecTecCall.«$dom_map» SpecTec.id SpecTec.value (globalInstLayer.FRAME (instContext.GLOBAL IC))⟩) (fun («exec:1» : (set SpecTec.id)) => (let «eval:0» : (set SpecTec.id) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$in_set» SpecTec.id id «eval:0»⟩) (fun («exec:2» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:2»; (.bind (.guard ((¬ («eval:1» = true)))) (fun (_ : Unit) => (.bind (.call ⟨(map SpecTec.id SpecTec.value), SpecTecCall.«$add_map» SpecTec.id SpecTec.value (globalInstLayer.FRAME (instContext.GLOBAL IC)) id value⟩) (fun («exec:3» : (map SpecTec.id SpecTec.value)) => (let «eval:2» : (map SpecTec.id SpecTec.value) := «exec:3»; (let frame : SpecTec.frame := «eval:2»; (.pure ((({ IC with GLOBAL := ({ (instContext.GLOBAL IC) with FRAME := frame } : globalInstLayer) } : instContext) : instContext)))))))))))))))))))))


noncomputable def «$add_var_i:clause:1» (input0 : cursor) (input1 : instContext) (input2 : SpecTec.id) (input3 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let IC : instContext := input1; (let id : SpecTec.id := input2; (let value : SpecTec.value := input3; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (.bind (.call ⟨(set SpecTec.id), SpecTecCall.«$dom_map» SpecTec.id SpecTec.value (blockInstLayer.FRAME (instContext.BLOCK IC))⟩) (fun («exec:1» : (set SpecTec.id)) => (let «eval:0» : (set SpecTec.id) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$in_set» SpecTec.id id «eval:0»⟩) (fun («exec:2» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:2»; (.bind (.guard ((¬ («eval:1» = true)))) (fun (_ : Unit) => (.bind (.call ⟨(map SpecTec.id SpecTec.value), SpecTecCall.«$add_map» SpecTec.id SpecTec.value (blockInstLayer.FRAME (instContext.BLOCK IC)) id value⟩) (fun («exec:3» : (map SpecTec.id SpecTec.value)) => (let «eval:2» : (map SpecTec.id SpecTec.value) := «exec:3»; (let frame : SpecTec.frame := «eval:2»; (.pure ((({ IC with BLOCK := ({ (instContext.BLOCK IC) with FRAME := frame } : blockInstLayer) } : instContext) : instContext)))))))))))))))))))))


noncomputable def «$add_var_i:clause:2» (input0 : cursor) (input1 : instContext) (input2 : SpecTec.id) (input3 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let IC : instContext := input1; (let id : SpecTec.id := input2; (let value : SpecTec.value := input3; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (let «frame*» : (_root_.List frame) := (localInstLayer.FRAMES (instContext.LOCAL IC)); (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «frame*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «frame*» with | «exec:2» :: «exec:1» => (let frame_h : frame := «exec:2»; (let «frame_t*» : (_root_.List frame) := «exec:1»; (.bind (.call ⟨(set SpecTec.id), SpecTecCall.«$dom_map» SpecTec.id SpecTec.value frame_h⟩) (fun («exec:3» : (set SpecTec.id)) => (let «eval:0» : (set SpecTec.id) := «exec:3»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$in_set» SpecTec.id id «eval:0»⟩) (fun («exec:4» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:4»; (.bind (.guard ((¬ («eval:1» = true)))) (fun (_ : Unit) => (.bind (.call ⟨(map SpecTec.id SpecTec.value), SpecTecCall.«$add_map» SpecTec.id SpecTec.value frame_h id value⟩) (fun («exec:5» : (map SpecTec.id SpecTec.value)) => (let «eval:2» : (map SpecTec.id SpecTec.value) := «exec:5»; (let frame_h' : frame := «eval:2»; (.pure ((({ IC with LOCAL := ({ (instContext.LOCAL IC) with FRAMES := (frame_h' :: «frame_t*») } : localInstLayer) } : instContext) : instContext))))))))))))))))) | [] => .unmatch))))))))))


noncomputable def «$add_var_i_clauses» (input0 : cursor) (input1 : instContext) (input2 : id) (input3 : value) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_var_i:clause:0»  input0 input1 input2 input3), fun (_ : _root_.Unit) => («$add_var_i:clause:1»  input0 input1 input2 input3), fun (_ : _root_.Unit) => («$add_var_i:clause:2»  input0 input1 input2 input3)]


noncomputable def «$add_vars_i:clause:0» (input0 : cursor) (input1 : instContext) (input2 : (_root_.List id)) (input3 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let IC : instContext := input1; (let «id*» : (_root_.List id) := input2; (let «value*» : (_root_.List value) := input3; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «id*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «value*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((IC : instContext)))))))))))


noncomputable def «$add_vars_i:clause:1» (input0 : cursor) (input1 : instContext) (input2 : (_root_.List id)) (input3 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let IC : instContext := input1; (let «id*» : (_root_.List id) := input2; (let «value*» : (_root_.List value) := input3; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «id*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «id*» with | «exec:2» :: «exec:1» => (let id_h : id := «exec:2»; (let «id_t*» : (_root_.List id) := «exec:1»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «value*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «value*» with | «exec:4» :: «exec:3» => (let value_h : value := «exec:4»; (let «value_t*» : (_root_.List value) := «exec:3»; (.bind (.call ⟨instContext, SpecTecCall.«$add_var_i» p IC id_h value_h⟩) (fun («exec:5» : instContext) => (let «eval:0» : instContext := «exec:5»; (let IC' : instContext := «eval:0»; (.bind (.call ⟨instContext, SpecTecCall.«$add_vars_i» p IC' «id_t*» «value_t*»⟩) (fun («exec:6» : instContext) => (let «eval:1» : instContext := «exec:6»; (let IC'' : instContext := «eval:1»; (.pure ((IC'' : instContext))))))))))))) | [] => .unmatch))))) | [] => .unmatch)))))))


noncomputable def «$add_vars_i_clauses» (input0 : cursor) (input1 : instContext) (input2 : (_root_.List id)) (input3 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_vars_i:clause:0»  input0 input1 input2 input3), fun (_ : _root_.Unit) => («$add_vars_i:clause:1»  input0 input1 input2 input3)]


noncomputable def «$add_type_i:clause:0» (input0 : cursor) (input1 : instContext) (input2 : SpecTec.typeId) (input3 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let IC : instContext := input1; (let typeId : SpecTec.typeId := input2; (let typeIR : SpecTec.typeIR := input3; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (.bind (.call ⟨(map SpecTec.typeId SpecTec.typeIR), SpecTecCall.«$add_map» SpecTec.typeId SpecTec.typeIR (blockInstLayer.TYPE (instContext.BLOCK IC)) typeId typeIR⟩) (fun («exec:1» : (map SpecTec.typeId SpecTec.typeIR)) => (let «eval:0» : (map SpecTec.typeId SpecTec.typeIR) := «exec:1»; (let theta : SpecTec.theta := «eval:0»; (.pure ((({ IC with BLOCK := ({ (instContext.BLOCK IC) with TYPE := theta } : blockInstLayer) } : instContext) : instContext)))))))))))))


noncomputable def «$add_type_i:clause:1» (input0 : cursor) (input1 : instContext) (input2 : SpecTec.typeId) (input3 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let IC : instContext := input1; (let typeId : SpecTec.typeId := input2; (let typeIR : SpecTec.typeIR := input3; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (.bind (.call ⟨(map SpecTec.typeId SpecTec.typeIR), SpecTecCall.«$add_map» SpecTec.typeId SpecTec.typeIR (localInstLayer.TYPE (instContext.LOCAL IC)) typeId typeIR⟩) (fun («exec:1» : (map SpecTec.typeId SpecTec.typeIR)) => (let «eval:0» : (map SpecTec.typeId SpecTec.typeIR) := «exec:1»; (let theta : SpecTec.theta := «eval:0»; (.pure ((({ IC with LOCAL := ({ (instContext.LOCAL IC) with TYPE := theta } : localInstLayer) } : instContext) : instContext)))))))))))))


noncomputable def «$add_type_i_clauses» (input0 : cursor) (input1 : instContext) (input2 : typeId) (input3 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_type_i:clause:0»  input0 input1 input2 input3), fun (_ : _root_.Unit) => («$add_type_i:clause:1»  input0 input1 input2 input3)]


noncomputable def «$add_types_i:clause:0» (input0 : cursor) (input1 : instContext) (input2 : (_root_.List typeId)) (input3 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let IC : instContext := input1; (let «typeId*» : (_root_.List typeId) := input2; (let «typeIR*» : (_root_.List typeIR) := input3; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeId*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeIR*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((IC : instContext)))))))))))


noncomputable def «$add_types_i:clause:1» (input0 : cursor) (input1 : instContext) (input2 : (_root_.List typeId)) (input3 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let IC : instContext := input1; (let «typeId*» : (_root_.List typeId) := input2; (let «typeIR*» : (_root_.List typeIR) := input3; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeId*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «typeId*» with | «exec:2» :: «exec:1» => (let typeId_h : typeId := «exec:2»; (let «typeId_t*» : (_root_.List typeId) := «exec:1»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «typeIR*» with | «exec:4» :: «exec:3» => (let typeIR_h : typeIR := «exec:4»; (let «typeIR_t*» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨instContext, SpecTecCall.«$add_type_i» p IC typeId_h typeIR_h⟩) (fun («exec:5» : instContext) => (let «eval:0» : instContext := «exec:5»; (let IC' : instContext := «eval:0»; (.bind (.call ⟨instContext, SpecTecCall.«$add_types_i» p IC' «typeId_t*» «typeIR_t*»⟩) (fun («exec:6» : instContext) => (let «eval:1» : instContext := «exec:6»; (.pure ((«eval:1» : instContext)))))))))))) | [] => .unmatch))))) | [] => .unmatch)))))))


noncomputable def «$add_types_i_clauses» (input0 : cursor) (input1 : instContext) (input2 : (_root_.List typeId)) (input3 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_types_i:clause:0»  input0 input1 input2 input3), fun (_ : _root_.Unit) => («$add_types_i:clause:1»  input0 input1 input2 input3)]


noncomputable def «ConstDecl_inst:clause:0» (input0 : cursor) (input1 : instContext) (input2 : constantDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let IC_0 : instContext := input1; (match input2 with | .«% CONST % % % ';'» «exec:1» «exec:2» «exec:3» «exec:4» => (let annotationList : SpecTec.annotationList := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (let nameIR : SpecTec.nameIR := «exec:3»; (match «exec:4» with | .«'=' _VALUE %» «exec:5» => (let value : SpecTec.value := «exec:5»; (.bind (.call ⟨instContext, SpecTecCall.«$add_var_i» p IC_0 nameIR value⟩) (fun («exec:6» : instContext) => (let «eval:0» : instContext := «exec:6»; (let IC_1 : instContext := «eval:0»; (.pure ((IC_1 : instContext)))))))))))))))


noncomputable def ConstDecl_inst_clauses (input0 : cursor) (input1 : instContext) (input2 : constantDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («ConstDecl_inst:clause:0»  input0 input1 input2)]


noncomputable def «$inherit_e:clause:0» (input0 : cursor) (input1 : evalContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let EC : evalContext := input1; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (.bind (.call ⟨theta, SpecTecCall.«$empty_theta»⟩) (fun («exec:1» : theta) => (let «eval:0» : theta := «exec:1»; (.bind (.call ⟨callableDefEnv, SpecTecCall.«$empty_callableDefEnv»⟩) (fun («exec:2» : callableDefEnv) => (let «eval:1» : callableDefEnv := «exec:2»; (.bind (.call ⟨stateEnv, SpecTecCall.«$empty_stateEnv»⟩) (fun («exec:3» : stateEnv) => (let «eval:2» : stateEnv := «exec:3»; (.bind (.call ⟨frame, SpecTecCall.«$empty_frame»⟩) (fun («exec:4» : frame) => (let «eval:3» : frame := «exec:4»; (let blockEvalLayer : SpecTec.blockEvalLayer := ({ TYPE := «eval:0», CALLABLE := «eval:1», STATE := «eval:2», FRAME := «eval:3» } : blockInstLayer); (.bind (.call ⟨theta, SpecTecCall.«$empty_theta»⟩) (fun («exec:5» : theta) => (let «eval:4» : theta := «exec:5»; (.bind (.call ⟨frame, SpecTecCall.«$empty_frame»⟩) (fun («exec:6» : frame) => (let «eval:5» : frame := «exec:6»; (let localEvalLayer : SpecTec.localEvalLayer := ({ TYPE := «eval:4», FRAMES := ([«eval:5»] : (_root_.List frame)) } : localInstLayer); (.pure ((({ ({ EC with BLOCK := blockEvalLayer } : evalContext) with LOCAL := localEvalLayer } : evalContext) : evalContext)))))))))))))))))))))))))))


noncomputable def «$inherit_e:clause:1» (input0 : cursor) (input1 : evalContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let EC : evalContext := input1; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (.bind (.call ⟨theta, SpecTecCall.«$empty_theta»⟩) (fun («exec:1» : theta) => (let «eval:0» : theta := «exec:1»; (.bind (.call ⟨frame, SpecTecCall.«$empty_frame»⟩) (fun («exec:2» : frame) => (let «eval:1» : frame := «exec:2»; (let localEvalLayer : SpecTec.localEvalLayer := ({ TYPE := «eval:0», FRAMES := ([«eval:1»] : (_root_.List frame)) } : localInstLayer); (.pure ((({ EC with LOCAL := localEvalLayer } : evalContext) : evalContext))))))))))))))


noncomputable def «$inherit_e:clause:2» (input0 : cursor) (input1 : evalContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let EC : evalContext := input1; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (.pure ((EC : evalContext)))))))


noncomputable def «$inherit_e_clauses» (input0 : cursor) (input1 : evalContext) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$inherit_e:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$inherit_e:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$inherit_e:clause:2»  input0 input1)]


noncomputable def «$copy_e:clause:0» (input0 : cursor) (input1 : evalContext) (input2 : evalContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let EC_from : evalContext := input1; (let EC_to : evalContext := input2; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (.pure ((({ EC_to with GLOBAL := (evalContext.GLOBAL EC_from) } : evalContext) : evalContext))))))))


noncomputable def «$copy_e:clause:1» (input0 : cursor) (input1 : evalContext) (input2 : evalContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let EC_from : evalContext := input1; (let EC_to : evalContext := input2; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (.pure ((({ ({ EC_to with GLOBAL := (evalContext.GLOBAL EC_from) } : evalContext) with BLOCK := (evalContext.BLOCK EC_from) } : evalContext) : evalContext))))))))


noncomputable def «$copy_e:clause:2» (input0 : cursor) (input1 : evalContext) (input2 : evalContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let EC_from : evalContext := input1; (let EC_to : evalContext := input2; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (.pure ((({ ({ ({ EC_to with GLOBAL := (evalContext.GLOBAL EC_from) } : evalContext) with BLOCK := (evalContext.BLOCK EC_from) } : evalContext) with LOCAL := (evalContext.LOCAL EC_from) } : evalContext) : evalContext))))))))


noncomputable def «$copy_e_clauses» (input0 : cursor) (input1 : evalContext) (input2 : evalContext) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$copy_e:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$copy_e:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$copy_e:clause:2»  input0 input1 input2)]


noncomputable def «$find_type_e:clause:0» (input0 : cursor) (input1 : evalContext) (input2 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let EC : evalContext := input1; (let nameIR : SpecTec.nameIR := input2; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.Option typeIR), SpecTecCall.«$find_map» typeId typeIR (blockInstLayer.TYPE (evalContext.BLOCK EC)) nameIR⟩) (fun («exec:1» : (_root_.Option typeIR)) => (let «eval:0» : (_root_.Option typeIR) := «exec:1»; (.pure ((«eval:0» : (_root_.Option typeIR))))))))))))


noncomputable def «$find_type_e:clause:1» (input0 : cursor) (input1 : evalContext) (input2 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let EC : evalContext := input1; (let nameIR : SpecTec.nameIR := input2; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.Option SpecTec.typeIR), SpecTecCall.«$find_map» typeId SpecTec.typeIR (localInstLayer.TYPE (evalContext.LOCAL EC)) nameIR⟩) (fun («exec:1» : (_root_.Option SpecTec.typeIR)) => (let «eval:0» : (_root_.Option SpecTec.typeIR) := «exec:1»; (let typeIR'? : (_root_.Option SpecTec.typeIR) := «eval:0»; (.bind (.guard (((_root_.Option.isSome typeIR'?) = true))) (fun (_ : Unit) => (match typeIR'? with | some «exec:2» => (let typeIR : SpecTec.typeIR := «exec:2»; (.pure (((_root_.Option.some typeIR) : (_root_.Option SpecTec.typeIR))))) | none => .unmatch))))))))))))

end SpecTec
