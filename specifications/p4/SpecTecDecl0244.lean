import SpecTecDecl0243

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$find_type_e:clause:2» (input0 : cursor) (input1 : evalContext) (input2 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let EC : evalContext := input1; (let nameIR : SpecTec.nameIR := input2; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (.bind (.call ⟨(_root_.Option typeIR), SpecTecCall.«$find_map» typeId typeIR (localInstLayer.TYPE (evalContext.LOCAL EC)) nameIR⟩) (fun («exec:1» : (_root_.Option typeIR)) => (let «eval:0» : (_root_.Option typeIR) := «exec:1»; (match «eval:0» with | none => (.bind (.call ⟨(_root_.Option typeIR), SpecTecCall.«$find_type_e» ((cursor.BLOCK) : cursor) EC nameIR⟩) (fun («exec:2» : (_root_.Option typeIR)) => (let «eval:1» : (_root_.Option typeIR) := «exec:2»; (.pure ((«eval:1» : (_root_.Option typeIR))))))) | some _ => .unmatch)))))))))


noncomputable def «$find_type_e_clauses» (input0 : cursor) (input1 : evalContext) (input2 : nameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_type_e:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$find_type_e:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$find_type_e:clause:2»  input0 input1 input2)]


noncomputable def «$directionless_trailing':clause:0» (input0 : _root_.Bool) (input1 : (_root_.List direction)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _b : _root_.Bool := input0; (let «direction*» : (_root_.List direction) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «direction*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))))


noncomputable def «$directionless_trailing':clause:1» (input0 : _root_.Bool) (input1 : (_root_.List SpecTec.direction)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let b : _root_.Bool := input0; (let «direction'*» : (_root_.List SpecTec.direction) := input1; (.bind (.guard (true = b)) (fun (_ : Unit) => (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «direction'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «direction'*» with | «exec:2» :: «exec:1» => (let direction : SpecTec.direction := «exec:2»; (let «direction_t*» : (_root_.List SpecTec.direction) := «exec:1»; (.bind (.guard (((«exec:match:direction:_EMPTY» direction) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$directionless_trailing'» true «direction_t*»⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | [] => .unmatch)))))))


noncomputable def «$directionless_trailing':clause:2» (input0 : _root_.Bool) (input1 : (_root_.List SpecTec.direction)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let b : _root_.Bool := input0; (let «direction'*» : (_root_.List SpecTec.direction) := input1; (.bind (.guard (false = b)) (fun (_ : Unit) => (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «direction'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «direction'*» with | «exec:2» :: «exec:1» => (let direction : SpecTec.direction := «exec:2»; (let «direction_t*» : (_root_.List SpecTec.direction) := «exec:1»; (.bind (.guard (((«exec:match:direction:_EMPTY» direction) = true))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))) | [] => .unmatch)))))))


noncomputable def «$directionless_trailing':clause:3» (input0 : _root_.Bool) (input1 : (_root_.List direction)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _b : _root_.Bool := input0; (let «direction*» : (_root_.List direction) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «direction*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «direction*» with | «exec:2» :: «exec:1» => (let direction_h : direction := «exec:2»; (let «direction_t*» : (_root_.List direction) := «exec:1»; (.bind (.guard ((direction_h ≠ ((direction._EMPTY) : direction)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$directionless_trailing'» false «direction_t*»⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | [] => .unmatch)))))


noncomputable def «$directionless_trailing'_clauses» (input0 : _root_.Bool) (input1 : (_root_.List direction)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$directionless_trailing':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$directionless_trailing':clause:1»  input0 input1), fun (_ : _root_.Unit) => («$directionless_trailing':clause:2»  input0 input1), fun (_ : _root_.Unit) => («$directionless_trailing':clause:3»  input0 input1)]


noncomputable def «$directionless_trailing:clause:0» (input0 : (_root_.List direction)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «direction*» : (_root_.List direction) := input0; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$directionless_trailing'» true («$rev_» (X := direction) «direction*»)⟩) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.pure ((«eval:0» : _root_.Bool)))))))


noncomputable def «$directionless_trailing_clauses» (input0 : (_root_.List direction)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$directionless_trailing:clause:0»  input0)]


noncomputable def «$split_dataplane_parameters:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «parameterIR*» : (_root_.List parameterIR) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «parameterIR*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure (((([] : (_root_.List parameterIR)), ([] : (_root_.List parameterIR))) : ((_root_.List parameterIR) × (_root_.List parameterIR))))))))


noncomputable def «$split_dataplane_parameters:clause:1» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «parameterIR*» : (_root_.List parameterIR) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «parameterIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «parameterIR*» with | «exec:2» :: «exec:1» => (let parameterIR_h : parameterIR := «exec:2»; (let «parameterIR_t*» : (_root_.List parameterIR) := «exec:1»; (match parameterIR_h with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let direction : SpecTec.direction := «exec:4»; (let _typeIR : typeIR := «exec:5»; (let _id : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.guard (((«exec:match:direction:_EMPTY» direction) = true))) (fun (_ : Unit) => (.bind (.call ⟨((_root_.List parameterIR) × (_root_.List parameterIR)), SpecTecCall.«$split_dataplane_parameters» «parameterIR_t*»⟩) (fun («exec:8» : ((_root_.List parameterIR) × (_root_.List parameterIR))) => (let «eval:0» : ((_root_.List parameterIR) × (_root_.List parameterIR)) := «exec:8»; (let «parameterIR_data*» : (_root_.List parameterIR) := («eval:0»).1; (let «parameterIR_control*» : (_root_.List parameterIR) := («eval:0»).2; (.pure (((«parameterIR_data*», (parameterIR_h :: «parameterIR_control*»)) : ((_root_.List parameterIR) × (_root_.List parameterIR)))))))))))))))))))) | [] => .unmatch))))


noncomputable def «$split_dataplane_parameters:clause:2» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «parameterIR*» : (_root_.List parameterIR) := input0; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «parameterIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «parameterIR*» with | «exec:2» :: «exec:1» => (let parameterIR_h : parameterIR := «exec:2»; (let «parameterIR_t*» : (_root_.List parameterIR) := «exec:1»; (match parameterIR_h with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let direction : SpecTec.direction := «exec:4»; (let _typeIR : typeIR := «exec:5»; (let _id : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.guard ((direction ≠ ((SpecTec.direction._EMPTY) : SpecTec.direction)))) (fun (_ : Unit) => (.bind (.call ⟨((_root_.List parameterIR) × (_root_.List parameterIR)), SpecTecCall.«$split_dataplane_parameters» «parameterIR_t*»⟩) (fun («exec:8» : ((_root_.List parameterIR) × (_root_.List parameterIR))) => (let «eval:0» : ((_root_.List parameterIR) × (_root_.List parameterIR)) := «exec:8»; (let «parameterIR_data*» : (_root_.List parameterIR) := («eval:0»).1; (let «parameterIR_control*» : (_root_.List parameterIR) := («eval:0»).2; (.pure ((((parameterIR_h :: «parameterIR_data*»), «parameterIR_control*») : ((_root_.List parameterIR) × (_root_.List parameterIR)))))))))))))))))))) | [] => .unmatch))))


noncomputable def «$split_dataplane_parameters_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$split_dataplane_parameters:clause:0»  input0), fun (_ : _root_.Unit) => («$split_dataplane_parameters:clause:1»  input0), fun (_ : _root_.Unit) => («$split_dataplane_parameters:clause:2»  input0)]


noncomputable def «$flatten_externConstructorOrMethodPrototypeList:clause:0» (input0 : SpecTec.externConstructorOrMethodPrototypeList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externConstructorOrMethodPrototypeList : SpecTec.externConstructorOrMethodPrototypeList := input0; (.bind (.guard (((«exec:match:externConstructorOrMethodPrototypeList:_EMPTY» externConstructorOrMethodPrototypeList) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List externConstructorOrMethodPrototype)) : (_root_.List externConstructorOrMethodPrototype)))))))


noncomputable def «$flatten_externConstructorOrMethodPrototypeList:clause:1» (input0 : SpecTec.externConstructorOrMethodPrototypeList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externConstructorOrMethodPrototypeList' : SpecTec.externConstructorOrMethodPrototypeList := input0; (.bind (.guard (((«exec:match:externConstructorOrMethodPrototypeList:% %» externConstructorOrMethodPrototypeList') = true))) (fun (_ : Unit) => (match externConstructorOrMethodPrototypeList' with | .«% %» «exec:1» «exec:2» => (let externConstructorOrMethodPrototypeList : SpecTec.externConstructorOrMethodPrototypeList := «exec:1»; (let externConstructorOrMethodPrototype : SpecTec.externConstructorOrMethodPrototype := «exec:2»; (.bind (.call ⟨(_root_.List SpecTec.externConstructorOrMethodPrototype), SpecTecCall.«$flatten_externConstructorOrMethodPrototypeList» externConstructorOrMethodPrototypeList⟩) (fun («exec:3» : (_root_.List SpecTec.externConstructorOrMethodPrototype)) => (let «eval:0» : (_root_.List SpecTec.externConstructorOrMethodPrototype) := «exec:3»; (.pure (((«eval:0» ++ ([externConstructorOrMethodPrototype] : (_root_.List SpecTec.externConstructorOrMethodPrototype))) : (_root_.List SpecTec.externConstructorOrMethodPrototype))))))))) | _ => .unmatch))))


noncomputable def «$flatten_externConstructorOrMethodPrototypeList_clauses» (input0 : externConstructorOrMethodPrototypeList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_externConstructorOrMethodPrototypeList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_externConstructorOrMethodPrototypeList:clause:1»  input0)]


noncomputable def «$parameterListIR_of_externMethodDef:clause:0» (input0 : SpecTec.externMethodDef) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externMethodDef : SpecTec.externMethodDef := input0; (.bind (.guard (((«exec:match:externMethodDef:EXTERN_METHOD % `< % `> `( % `) %» externMethodDef) = true))) (fun (_ : Unit) => (match externMethodDef with | .«EXTERN_METHOD % `< % `> `( % `) %» «exec:1» «exec:2» «exec:3» «exec:4» => (let _nameIR : nameIR := «exec:1»; (let _typeParameterListIR : typeParameterListIR := «exec:2»; (let parameterListIR : SpecTec.parameterListIR := «exec:3»; (let _blockStatementIR? : (_root_.Option blockStatementIR) := «exec:4»; (.pure ((parameterListIR : (_root_.List parameterIR)))))))) | _ => .unmatch))))


noncomputable def «$parameterListIR_of_externMethodDef_clauses» (input0 : externMethodDef) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$parameterListIR_of_externMethodDef:clause:0»  input0)]


noncomputable def «$type_of_externMethodPrototypeIR:clause:0» (input0 : SpecTec.externMethodPrototypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externMethodPrototypeIR : SpecTec.externMethodPrototypeIR := input0; (.bind (.guard (((«exec:match:externMethodPrototypeIR:% % ';'» externMethodPrototypeIR) = true))) (fun (_ : Unit) => (match externMethodPrototypeIR with | .«% % ';'» «exec:1» «exec:2» => (let _annotationList : annotationList := «exec:1»; (match «exec:2» with | .«% % `< % ',' % `> `( % `)» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let typeIR_ret : typeIR := «exec:3»; (let nameIR : SpecTec.nameIR := «exec:4»; (let typeParameterListIR_expl : typeParameterListIR := «exec:5»; (let typeParameterListIR_impl : typeParameterListIR := «exec:6»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:7»; (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := ((SpecTec.externMethodTypeDefIR.«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» nameIR typeParameterListIR_expl typeParameterListIR_impl «parameterIR*» typeIR_ret) : SpecTec.externMethodTypeDefIR); (.pure ((externMethodTypeDefIR : SpecTec.externMethodTypeDefIR))))))))))) | _ => .unmatch))))


noncomputable def «$type_of_externMethodPrototypeIR:clause:1» (input0 : SpecTec.externMethodPrototypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externMethodPrototypeIR : SpecTec.externMethodPrototypeIR := input0; (.bind (.guard (((«exec:match:externMethodPrototypeIR:% ABSTRACT % ';'» externMethodPrototypeIR) = true))) (fun (_ : Unit) => (match externMethodPrototypeIR with | .«% ABSTRACT % ';'» «exec:1» «exec:2» => (let _annotationList : annotationList := «exec:1»; (match «exec:2» with | .«% % `< % ',' % `> `( % `)» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let typeIR_ret : typeIR := «exec:3»; (let nameIR : SpecTec.nameIR := «exec:4»; (let typeParameterListIR_expl : typeParameterListIR := «exec:5»; (let typeParameterListIR_impl : typeParameterListIR := «exec:6»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:7»; (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := ((SpecTec.externMethodTypeDefIR.«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» nameIR typeParameterListIR_expl typeParameterListIR_impl «parameterIR*» typeIR_ret) : SpecTec.externMethodTypeDefIR); (.pure ((externMethodTypeDefIR : SpecTec.externMethodTypeDefIR))))))))))) | _ => .unmatch))))


noncomputable def «$type_of_externMethodPrototypeIR_clauses» (input0 : externMethodPrototypeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$type_of_externMethodPrototypeIR:clause:0»  input0), fun (_ : _root_.Unit) => («$type_of_externMethodPrototypeIR:clause:1»  input0)]


noncomputable def «Decl_ok:externObjectDeclaration:iter:7:clause:0» (input0 : (_root_.List externMethodPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List externMethodTypeDefIR)) : (_root_.List externMethodTypeDefIR)))) | _ :: _ => .unmatch)


noncomputable def «Decl_ok:externObjectDeclaration:iter:7:clause:1» (input0 : (_root_.List SpecTec.externMethodPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let externMethodPrototypeIR : SpecTec.externMethodPrototypeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.externMethodPrototypeIR) := «exec:1»; (.bind (.call ⟨SpecTec.externMethodTypeDefIR, SpecTecCall.«$type_of_externMethodPrototypeIR» externMethodPrototypeIR⟩) (fun («exec:3» : SpecTec.externMethodTypeDefIR) => (let «eval:8» : SpecTec.externMethodTypeDefIR := «exec:3»; (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := «eval:8»; (.bind (.call ⟨(_root_.List SpecTec.externMethodTypeDefIR), SpecTecCall.«Decl_ok:externObjectDeclaration:iter:7» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.externMethodTypeDefIR)) => (let «tail:1» : (_root_.List SpecTec.externMethodTypeDefIR) := «exec:4»; (.pure (((externMethodTypeDefIR :: «tail:1») : (_root_.List SpecTec.externMethodTypeDefIR))))))))))))) | [] => .unmatch)


noncomputable def «Decl_ok:externObjectDeclaration:iter:7_clauses» (input0 : (_root_.List externMethodPrototypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:externObjectDeclaration:iter:7:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_ok:externObjectDeclaration:iter:7:clause:1»  input0)]


noncomputable def «ExternMethod_inst:clause:0» (input0 : instContext) (input1 : SpecTec.externMethodPrototypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let IC_0 : instContext := input0; (let externMethodPrototypeIR : SpecTec.externMethodPrototypeIR := input1; (let externMethodPrototypeIR' : SpecTec.externMethodPrototypeIR := externMethodPrototypeIR; (.bind (.guard (((«exec:match:externMethodPrototypeIR:% % ';'» externMethodPrototypeIR') = true))) (fun (_ : Unit) => (match externMethodPrototypeIR' with | .«% % ';'» «exec:1» «exec:2» => (let annotationList : SpecTec.annotationList := «exec:1»; (match «exec:2» with | .«% % `< % ',' % `> `( % `)» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let typeIR : SpecTec.typeIR := «exec:3»; (let nameIR : SpecTec.nameIR := «exec:4»; (let typeParameterListIR : SpecTec.typeParameterListIR := «exec:5»; (let typeParameterListIR_inferred : SpecTec.typeParameterListIR := «exec:6»; (let parameterListIR : SpecTec.parameterListIR := «exec:7»; (.bind (.call ⟨SpecTec.callableId, SpecTecCall.«$callableId_IR» nameIR parameterListIR⟩) (fun («exec:8» : SpecTec.callableId) => (let «eval:0» : SpecTec.callableId := «exec:8»; (let callableId : SpecTec.callableId := «eval:0»; (let externMethodDef : SpecTec.externMethodDef := ((SpecTec.externMethodDef.«EXTERN_METHOD % `< % `> `( % `) %» nameIR (typeParameterListIR ++ typeParameterListIR_inferred) parameterListIR ((_root_.Option.none) : (_root_.Option blockStatementIR))) : SpecTec.externMethodDef); (.bind (.call ⟨instContext, SpecTecCall.«$add_callableDef_overload_i» ((cursor.BLOCK) : cursor) IC_0 callableId («cast:externMethodDef:callableDef» externMethodDef)⟩) (fun («exec:9» : instContext) => (let «eval:1» : instContext := «exec:9»; (let IC_1 : instContext := «eval:1»; (.pure ((IC_1 : instContext))))))))))))))))))) | _ => .unmatch))))))


noncomputable def «ExternMethod_inst:clause:1» (input0 : instContext) (input1 : SpecTec.externMethodPrototypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let IC_0 : instContext := input0; (let externMethodPrototypeIR : SpecTec.externMethodPrototypeIR := input1; (let externMethodPrototypeIR' : SpecTec.externMethodPrototypeIR := externMethodPrototypeIR; (.bind (.guard (((«exec:match:externMethodPrototypeIR:% ABSTRACT % ';'» externMethodPrototypeIR') = true))) (fun (_ : Unit) => (match externMethodPrototypeIR' with | .«% ABSTRACT % ';'» «exec:1» «exec:2» => (let annotationList : SpecTec.annotationList := «exec:1»; (match «exec:2» with | .«% % `< % ',' % `> `( % `)» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let typeIR : SpecTec.typeIR := «exec:3»; (let nameIR : SpecTec.nameIR := «exec:4»; (let typeParameterListIR : SpecTec.typeParameterListIR := «exec:5»; (let typeParameterListIR_inferred : SpecTec.typeParameterListIR := «exec:6»; (let parameterListIR : SpecTec.parameterListIR := «exec:7»; (.bind (.call ⟨SpecTec.callableId, SpecTecCall.«$callableId_IR» nameIR parameterListIR⟩) (fun («exec:8» : SpecTec.callableId) => (let «eval:0» : SpecTec.callableId := «exec:8»; (let callableId : SpecTec.callableId := «eval:0»; (let externMethodDef : SpecTec.externMethodDef := ((SpecTec.externMethodDef.«EXTERN_METHOD ABSTRACT % `< % `> `( % `)» nameIR (typeParameterListIR ++ typeParameterListIR_inferred) parameterListIR) : SpecTec.externMethodDef); (.bind (.call ⟨instContext, SpecTecCall.«$add_callableDef_overload_i» ((cursor.BLOCK) : cursor) IC_0 callableId («cast:externMethodDef:callableDef» externMethodDef)⟩) (fun («exec:9» : instContext) => (let «eval:1» : instContext := «exec:9»; (let IC_1 : instContext := «eval:1»; (.pure ((IC_1 : instContext))))))))))))))))))) | _ => .unmatch))))))


noncomputable def ExternMethod_inst_clauses (input0 : instContext) (input1 : externMethodPrototypeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («ExternMethod_inst:clause:0»  input0 input1), fun (_ : _root_.Unit) => («ExternMethod_inst:clause:1»  input0 input1)]


noncomputable def «ExternMethods_inst:clause:0» (input0 : instContext) (input1 : (_root_.List externMethodPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let IC' : instContext := input0; (let «externMethodPrototypeIR*» : (_root_.List externMethodPrototypeIR) := input1; (let IC : instContext := IC'; (.bind (.guard (([] : (_root_.List externMethodPrototypeIR)) = «externMethodPrototypeIR*»)) (fun (_ : Unit) => (.pure ((IC : instContext))))))))


noncomputable def «ExternMethods_inst:clause:1» (input0 : instContext) (input1 : (_root_.List externMethodPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let IC' : instContext := input0; (let «externMethodPrototypeIR*» : (_root_.List externMethodPrototypeIR) := input1; (let IC_0 : instContext := IC'; (let «externMethodPrototypeIR'*» : (_root_.List externMethodPrototypeIR) := «externMethodPrototypeIR*»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «externMethodPrototypeIR'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «externMethodPrototypeIR'*» with | «exec:2» :: «exec:1» => (let externMethodPrototypeIR_h : externMethodPrototypeIR := «exec:2»; (let «externMethodPrototypeIR_t*» : (_root_.List externMethodPrototypeIR) := «exec:1»; (.bind (.call ⟨instContext, SpecTecCall.ExternMethod_inst IC_0 externMethodPrototypeIR_h⟩) (fun («exec:3» : instContext) => (let IC_1 : instContext := «exec:3»; (.bind (.call ⟨instContext, SpecTecCall.ExternMethods_inst IC_1 «externMethodPrototypeIR_t*»⟩) (fun («exec:4» : instContext) => (let IC_2 : instContext := «exec:4»; (.pure ((IC_2 : instContext))))))))))) | [] => .unmatch)))))))


noncomputable def ExternMethods_inst_clauses (input0 : instContext) (input1 : (_root_.List externMethodPrototypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («ExternMethods_inst:clause:0»  input0 input1), fun (_ : _root_.Unit) => («ExternMethods_inst:clause:1»  input0 input1)]


noncomputable def «Decl_inst:non-constructor:iter:3:clause:0» (input0 : (_root_.List externMethodPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List externMethodTypeDefIR)) : (_root_.List externMethodTypeDefIR)))) | _ :: _ => .unmatch)


noncomputable def «Decl_inst:non-constructor:iter:3:clause:1» (input0 : (_root_.List SpecTec.externMethodPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let externMethodPrototypeIR : SpecTec.externMethodPrototypeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.externMethodPrototypeIR) := «exec:1»; (.bind (.call ⟨SpecTec.externMethodTypeDefIR, SpecTecCall.«$type_of_externMethodPrototypeIR» externMethodPrototypeIR⟩) (fun («exec:3» : SpecTec.externMethodTypeDefIR) => (let «eval:4» : SpecTec.externMethodTypeDefIR := «exec:3»; (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := «eval:4»; (.bind (.call ⟨(_root_.List SpecTec.externMethodTypeDefIR), SpecTecCall.«Decl_inst:non-constructor:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.externMethodTypeDefIR)) => (let «tail:1» : (_root_.List SpecTec.externMethodTypeDefIR) := «exec:4»; (.pure (((externMethodTypeDefIR :: «tail:1») : (_root_.List SpecTec.externMethodTypeDefIR))))))))))))) | [] => .unmatch)

end SpecTec
