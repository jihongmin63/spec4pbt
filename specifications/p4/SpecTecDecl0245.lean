import SpecTecDecl0244

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Decl_inst:non-constructor:iter:3_clauses» (input0 : (_root_.List externMethodPrototypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:non-constructor:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_inst:non-constructor:iter:3:clause:1»  input0)]


noncomputable def «Decl_inst:constructor:iter:3:clause:0» (input0 : (_root_.List externMethodPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List externMethodTypeDefIR)) : (_root_.List externMethodTypeDefIR)))) | _ :: _ => .unmatch)


noncomputable def «Decl_inst:constructor:iter:3:clause:1» (input0 : (_root_.List SpecTec.externMethodPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let externMethodPrototypeIR : SpecTec.externMethodPrototypeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.externMethodPrototypeIR) := «exec:1»; (.bind (.call ⟨SpecTec.externMethodTypeDefIR, SpecTecCall.«$type_of_externMethodPrototypeIR» externMethodPrototypeIR⟩) (fun («exec:3» : SpecTec.externMethodTypeDefIR) => (let «eval:4» : SpecTec.externMethodTypeDefIR := «exec:3»; (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := «eval:4»; (.bind (.call ⟨(_root_.List SpecTec.externMethodTypeDefIR), SpecTecCall.«Decl_inst:constructor:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.externMethodTypeDefIR)) => (let «tail:1» : (_root_.List SpecTec.externMethodTypeDefIR) := «exec:4»; (.pure (((externMethodTypeDefIR :: «tail:1») : (_root_.List SpecTec.externMethodTypeDefIR))))))))))))) | [] => .unmatch)


noncomputable def «Decl_inst:constructor:iter:3_clauses» (input0 : (_root_.List externMethodPrototypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:constructor:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_inst:constructor:iter:3:clause:1»  input0)]


noncomputable def «$callableId_of_externMethodPrototypeIR:clause:0» (input0 : SpecTec.externMethodPrototypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externMethodPrototypeIR : SpecTec.externMethodPrototypeIR := input0; (.bind (.guard (((«exec:match:externMethodPrototypeIR:% % ';'» externMethodPrototypeIR) = true))) (fun (_ : Unit) => (match externMethodPrototypeIR with | .«% % ';'» «exec:1» «exec:2» => (let _annotationList : annotationList := «exec:1»; (match «exec:2» with | .«% % `< % ',' % `> `( % `)» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _typeIR : typeIR := «exec:3»; (let nameIR : SpecTec.nameIR := «exec:4»; (let _typeParameterListIR : typeParameterListIR := «exec:5»; (let _typeParameterListIR' : typeParameterListIR := «exec:6»; (let parameterListIR : SpecTec.parameterListIR := «exec:7»; (.bind (.call ⟨callableId, SpecTecCall.«$callableId_IR» nameIR parameterListIR⟩) (fun («exec:8» : callableId) => (let «eval:0» : callableId := «exec:8»; (.pure ((«eval:0» : callableId))))))))))))) | _ => .unmatch))))


noncomputable def «$callableId_of_externMethodPrototypeIR:clause:1» (input0 : SpecTec.externMethodPrototypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externMethodPrototypeIR : SpecTec.externMethodPrototypeIR := input0; (.bind (.guard (((«exec:match:externMethodPrototypeIR:% ABSTRACT % ';'» externMethodPrototypeIR) = true))) (fun (_ : Unit) => (match externMethodPrototypeIR with | .«% ABSTRACT % ';'» «exec:1» «exec:2» => (let _annotationList : annotationList := «exec:1»; (match «exec:2» with | .«% % `< % ',' % `> `( % `)» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _typeIR : typeIR := «exec:3»; (let nameIR : SpecTec.nameIR := «exec:4»; (let _typeParameterListIR : typeParameterListIR := «exec:5»; (let _typeParameterListIR' : typeParameterListIR := «exec:6»; (let parameterListIR : SpecTec.parameterListIR := «exec:7»; (.bind (.call ⟨callableId, SpecTecCall.«$callableId_IR» nameIR parameterListIR⟩) (fun («exec:8» : callableId) => (let «eval:0» : callableId := «exec:8»; (.pure ((«eval:0» : callableId))))))))))))) | _ => .unmatch))))


noncomputable def «$callableId_of_externMethodPrototypeIR_clauses» (input0 : externMethodPrototypeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$callableId_of_externMethodPrototypeIR:clause:0»  input0), fun (_ : _root_.Unit) => («$callableId_of_externMethodPrototypeIR:clause:1»  input0)]


noncomputable def «Decl_inst:non-constructor:iter:1:clause:0» (input0 : (_root_.List externMethodPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List callableId)) : (_root_.List callableId)))) | _ :: _ => .unmatch)


noncomputable def «Decl_inst:non-constructor:iter:1:clause:1» (input0 : (_root_.List SpecTec.externMethodPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let externMethodPrototypeIR : SpecTec.externMethodPrototypeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.externMethodPrototypeIR) := «exec:1»; (.bind (.call ⟨callableId, SpecTecCall.«$callableId_of_externMethodPrototypeIR» externMethodPrototypeIR⟩) (fun («exec:3» : callableId) => (let «eval:2» : callableId := «exec:3»; (let callableId_method : callableId := «eval:2»; (.bind (.call ⟨(_root_.List callableId), SpecTecCall.«Decl_inst:non-constructor:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List callableId)) => (let «tail:1» : (_root_.List callableId) := «exec:4»; (.pure (((callableId_method :: «tail:1») : (_root_.List callableId))))))))))))) | [] => .unmatch)


noncomputable def «Decl_inst:non-constructor:iter:1_clauses» (input0 : (_root_.List externMethodPrototypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:non-constructor:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_inst:non-constructor:iter:1:clause:1»  input0)]


noncomputable def «Decl_inst:constructor:iter:1:clause:0» (input0 : (_root_.List externMethodPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List callableId)) : (_root_.List callableId)))) | _ :: _ => .unmatch)


noncomputable def «Decl_inst:constructor:iter:1:clause:1» (input0 : (_root_.List SpecTec.externMethodPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let externMethodPrototypeIR : SpecTec.externMethodPrototypeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.externMethodPrototypeIR) := «exec:1»; (.bind (.call ⟨callableId, SpecTecCall.«$callableId_of_externMethodPrototypeIR» externMethodPrototypeIR⟩) (fun («exec:3» : callableId) => (let «eval:2» : callableId := «exec:3»; (let callableId_method : callableId := «eval:2»; (.bind (.call ⟨(_root_.List callableId), SpecTecCall.«Decl_inst:constructor:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List callableId)) => (let «tail:1» : (_root_.List callableId) := «exec:4»; (.pure (((callableId_method :: «tail:1») : (_root_.List callableId))))))))))))) | [] => .unmatch)


noncomputable def «Decl_inst:constructor:iter:1_clauses» (input0 : (_root_.List externMethodPrototypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:constructor:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_inst:constructor:iter:1:clause:1»  input0)]


noncomputable def «$is_concrete_extern_object'':clause:0» (input0 : SpecTec.externMethodTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := input0; (.bind (.guard (((«exec:match:externMethodTypeDefIR:EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» externMethodTypeDefIR) = true))) (fun (_ : Unit) => (match externMethodTypeDefIR with | .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let _nameIR : nameIR := «exec:1»; (let «_typeParameterIR*» : (_root_.List typeParameterIR) := «exec:2»; (let «_typeParameterIR'*» : (_root_.List typeParameterIR) := «exec:3»; (let «_parameterIR*» : (_root_.List parameterIR) := «exec:4»; (let _typeIR : typeIR := «exec:5»; (.pure ((true : _root_.Bool)))))))) | _ => .unmatch))))


noncomputable def «$is_concrete_extern_object'':clause:1» (input0 : SpecTec.externMethodTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := input0; (.pure ((false : _root_.Bool))))


noncomputable def «$is_concrete_extern_object''_clauses» (input0 : externMethodTypeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_concrete_extern_object'':clause:0»  input0), fun (_ : _root_.Unit) => («$is_concrete_extern_object'':clause:1»  input0)]


noncomputable def «$is_concrete_extern_object':case_2:iter:3:clause:0» (input0 : (_root_.List externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «$is_concrete_extern_object':case_2:iter:3:clause:1» (input0 : (_root_.List SpecTec.externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.externMethodTypeDefIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_concrete_extern_object''» externMethodTypeDefIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:4» : _root_.Bool := «exec:3»; (.bind (.guard ((«eval:4» = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$is_concrete_extern_object':case_2:iter:3» «tail:0»⟩) (fun («exec:4» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | [] => .unmatch)


noncomputable def «$is_concrete_extern_object':case_2:iter:3_clauses» (input0 : (_root_.List externMethodTypeDefIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_concrete_extern_object':case_2:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$is_concrete_extern_object':case_2:iter:3:clause:1»  input0)]


noncomputable def «$parameterListIR_of_externMethodTypeDefIR:clause:0» (input0 : SpecTec.externMethodTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := input0; (.bind (.guard (((«exec:match:externMethodTypeDefIR:EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» externMethodTypeDefIR) = true))) (fun (_ : Unit) => (match externMethodTypeDefIR with | .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let _nameIR : nameIR := «exec:1»; (let «_typeParameterIR*» : (_root_.List typeParameterIR) := «exec:2»; (let «_typeParameterIR'*» : (_root_.List typeParameterIR) := «exec:3»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:4»; (let _typeIR : typeIR := «exec:5»; (.pure ((«parameterIR*» : (_root_.List parameterIR))))))))) | _ => .unmatch))))


noncomputable def «$parameterListIR_of_externMethodTypeDefIR:clause:1» (input0 : SpecTec.externMethodTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := input0; (.bind (.guard (((«exec:match:externMethodTypeDefIR:EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» externMethodTypeDefIR) = true))) (fun (_ : Unit) => (match externMethodTypeDefIR with | .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let _nameIR : nameIR := «exec:1»; (let «_typeParameterIR*» : (_root_.List typeParameterIR) := «exec:2»; (let «_typeParameterIR'*» : (_root_.List typeParameterIR) := «exec:3»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:4»; (let _typeIR : typeIR := «exec:5»; (.pure ((«parameterIR*» : (_root_.List parameterIR))))))))) | _ => .unmatch))))


noncomputable def «$parameterListIR_of_externMethodTypeDefIR_clauses» (input0 : externMethodTypeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$parameterListIR_of_externMethodTypeDefIR:clause:0»  input0), fun (_ : _root_.Unit) => («$parameterListIR_of_externMethodTypeDefIR:clause:1»  input0)]


noncomputable def «$join_flow:clause:0» (input0 : flow) (input1 : flow) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let f : flow := input0; (let f' : flow := input1; (.bind (.guard (((«exec:match:flow:RET» f) = true))) (fun (_ : Unit) => (.bind (.guard (((«exec:match:flow:RET» f') = true))) (fun (_ : Unit) => (.pure ((((flow.RET) : flow) : flow)))))))))


noncomputable def «$join_flow:clause:1» (input0 : flow) (input1 : flow) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let f_a : flow := input0; (let f_b : flow := input1; (.pure ((((flow.CONT) : flow) : flow)))))


noncomputable def «$join_flow_clauses» (input0 : flow) (input1 : flow) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$join_flow:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$join_flow:clause:1»  input0 input1)]


noncomputable def «$join_control_t:clause:0» (input0 : typingContext) (input1 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC_a : typingContext := input0; (let TC_b : typingContext := input1; (.bind (.call ⟨flow, SpecTecCall.«$join_flow» (typingContext.CONTROL TC_a) (typingContext.CONTROL TC_b)⟩) (fun («exec:1» : flow) => (let «eval:0» : flow := «exec:1»; (.pure ((«eval:0» : flow))))))))


noncomputable def «$join_control_t_clauses» (input0 : typingContext) (input1 : typingContext) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$join_control_t:clause:0»  input0 input1)]


noncomputable def «$resolve_constraint:clause:0» (input0 : SpecTec.strictness) (input1 : constraint) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let strictness : SpecTec.strictness := input0; (let «set<pair<typeId, infer>>» : (set (pair typeId infer)) := input1; (.bind (.guard (((set.«`{ % `}» ([] : (_root_.List (pair typeId infer)))) : (set (pair typeId infer))) = «set<pair<typeId, infer>>»)) (fun (_ : Unit) => (.pure ((((set.«`{ % `}» ([] : (_root_.List (pair typeId typeIR)))) : (set (pair typeId typeIR))) : inference)))))))


noncomputable def «$resolve_constraint:clause:1» (input0 : SpecTec.strictness) (input1 : constraint) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let strictness : SpecTec.strictness := input0; (match input1 with | .«`{ % `}» «exec:1» => (let «pair<typeId, infer>*» : (_root_.List (pair typeId SpecTec.infer)) := «exec:1»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «pair<typeId, infer>*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «pair<typeId, infer>*» with | «exec:3» :: «exec:2» => (match «exec:3» with | .«% ':' %» «exec:4» «exec:5» => (let typeId_h : typeId := «exec:4»; (let infer_h : SpecTec.infer := «exec:5»; (let «eval:1» : (_root_.List (pair typeId SpecTec.infer)) := «exec:2»; (.bind (.call ⟨((_root_.List SpecTec.infer) × (_root_.List typeId)), SpecTecCall.«$resolve_constraint:case_2:pattern-iter:0» «eval:1»⟩) (fun («exec:6» : ((_root_.List SpecTec.infer) × (_root_.List typeId))) => (let «infer_t*» : (_root_.List SpecTec.infer) := («exec:6»).1; (let «typeId_t*» : (_root_.List typeId) := («exec:6»).2; (let infer : SpecTec.infer := infer_h; (.bind (.guard (((«exec:match:infer:KNOWN AS %» infer) = true))) (fun (_ : Unit) => (match infer with | .«KNOWN AS %» «exec:7» => (let typeIR_h : typeIR := «exec:7»; (.bind (.call ⟨(_root_.List (pair _root_.String SpecTec.infer)), SpecTecCall.«$resolve_constraint:case_2:iter:2» «infer_t*» «typeId_t*»⟩) (fun («exec:8» : (_root_.List (pair _root_.String SpecTec.infer))) => (let «eval:3» : (_root_.List (pair typeId SpecTec.infer)) := «exec:8»; (.bind (.call ⟨inference, SpecTecCall.«$resolve_constraint» strictness ((set.«`{ % `}» «eval:3») : (set (pair typeId SpecTec.infer)))⟩) (fun («exec:9» : inference) => (let «eval:4» : inference := «exec:9»; (match «eval:4» with | .«`{ % `}» «exec:10» => (let «eval:6» : (_root_.List (pair typeId typeIR)) := «exec:10»; (.bind (.call ⟨((_root_.List typeIR) × (_root_.List typeId)), SpecTecCall.«$resolve_constraint:case_2:pattern-iter:5» «eval:6»⟩) (fun («exec:11» : ((_root_.List typeIR) × (_root_.List typeId))) => (let «typeIR_t*» : (_root_.List typeIR) := («exec:11»).1; (let «typeId*» : (_root_.List typeId) := («exec:11»).2; (.bind (.guard ((_root_.List.length «typeId*») = (_root_.List.length «typeId_t*»))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$resolve_constraint:case_2:iter:7» «typeId_t*» «typeId*»⟩) (fun («exec:12» : _root_.Unit) => (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$resolve_constraint:case_2:iter:8» «typeIR_t*» «typeId_t*»⟩) (fun («exec:13» : (_root_.List (pair _root_.String typeIR))) => (let «eval:9» : (_root_.List (pair typeId typeIR)) := «exec:13»; (.pure ((((set.«`{ % `}» (((pair.«% ':' %» typeId_h typeIR_h) : (pair typeId typeIR)) :: «eval:9»)) : (set (pair typeId typeIR))) : inference))))))))))))))))))))))) | _ => .unmatch)))))))))))) | [] => .unmatch))))))


noncomputable def «$resolve_constraint:clause:2» (input0 : SpecTec.strictness) (input1 : constraint) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let strictness : SpecTec.strictness := input0; (match input1 with | .«`{ % `}» «exec:1» => (let «pair<typeId, infer>*» : (_root_.List (pair typeId infer)) := «exec:1»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «pair<typeId, infer>*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «pair<typeId, infer>*» with | «exec:3» :: «exec:2» => (match «exec:3» with | .«% ':' %» «exec:4» «exec:5» => (let typeId_h : typeId := «exec:4»; (let infer_h : infer := «exec:5»; (let «eval:1» : (_root_.List (pair typeId infer)) := «exec:2»; (.bind (.call ⟨((_root_.List infer) × (_root_.List typeId)), SpecTecCall.«$resolve_constraint:case_3:pattern-iter:0» «eval:1»⟩) (fun («exec:6» : ((_root_.List infer) × (_root_.List typeId))) => (let «infer_t*» : (_root_.List infer) := («exec:6»).1; (let «typeId_t*» : (_root_.List typeId) := («exec:6»).2; (match infer_h with | .UNKNOWN  => (.bind (.call ⟨(_root_.Option strict), SpecTecCall.«$find_map» typeId strict strictness typeId_h⟩) (fun («exec:7» : (_root_.Option strict)) => (let «eval:2» : (_root_.Option strict) := «exec:7»; (.bind (.guard ((_root_.Option.some ((strict.LAX) : strict)) = «eval:2»)) (fun (_ : Unit) => (.bind (.call ⟨(_root_.List (pair _root_.String infer)), SpecTecCall.«$resolve_constraint:case_3:iter:3» «infer_t*» «typeId_t*»⟩) (fun («exec:8» : (_root_.List (pair _root_.String infer))) => (let «eval:4» : (_root_.List (pair typeId infer)) := «exec:8»; (.bind (.call ⟨inference, SpecTecCall.«$resolve_constraint» strictness ((set.«`{ % `}» «eval:4») : (set (pair typeId infer)))⟩) (fun («exec:9» : inference) => (let «eval:5» : inference := «exec:9»; (match «eval:5» with | .«`{ % `}» «exec:10» => (let «eval:7» : (_root_.List (pair typeId typeIR)) := «exec:10»; (.bind (.call ⟨((_root_.List typeIR) × (_root_.List typeId)), SpecTecCall.«$resolve_constraint:case_3:pattern-iter:6» «eval:7»⟩) (fun («exec:11» : ((_root_.List typeIR) × (_root_.List typeId))) => (let «typeIR_t*» : (_root_.List typeIR) := («exec:11»).1; (let «typeId*» : (_root_.List typeId) := («exec:11»).2; (.bind (.guard ((_root_.List.length «typeId*») = (_root_.List.length «typeId_t*»))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$resolve_constraint:case_3:iter:8» «typeId_t*» «typeId*»⟩) (fun («exec:12» : _root_.Unit) => (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$resolve_constraint:case_3:iter:9» «typeIR_t*» «typeId_t*»⟩) (fun («exec:13» : (_root_.List (pair _root_.String typeIR))) => (let «eval:10» : (_root_.List (pair typeId typeIR)) := «exec:13»; (.pure ((((set.«`{ % `}» (((pair.«% ':' %» typeId_h ((typeIR.BOOL) : typeIR)) : (pair typeId typeIR)) :: «eval:10»)) : (set (pair typeId typeIR))) : inference))))))))))))))))))))))))))) | _ => .unmatch))))))))) | [] => .unmatch))))))


noncomputable def «$resolve_constraint_clauses» (input0 : strictness) (input1 : constraint) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$resolve_constraint:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$resolve_constraint:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$resolve_constraint:clause:2»  input0 input1)]


noncomputable def «$flatten_objectDeclarationList:clause:0» (input0 : SpecTec.objectDeclarationList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let objectDeclarationList : SpecTec.objectDeclarationList := input0; (.bind (.guard (((«exec:match:objectDeclarationList:_EMPTY» objectDeclarationList) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List objectDeclaration)) : (_root_.List objectDeclaration)))))))

end SpecTec
