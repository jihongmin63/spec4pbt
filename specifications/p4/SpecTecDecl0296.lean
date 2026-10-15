import SpecTecDecl0295

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$result_concat:clause:6» (input0 : SpecTec.typeIR) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_l : SpecTec.typeIR := input0; (let typeIR : SpecTec.typeIR := input1; (.bind (.guard (((«sub:typeIR:typedefTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$result_concat:case_7:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : typedefTypeIR := «exec:1»; (match «eval:0» with | .TYPEDEF «exec:2» «exec:3» => (let _typeId : typeId := «exec:2»; (let typeIR_r : SpecTec.typeIR := «exec:3»; (.bind (.guard ((¬ ((«sub:typeIR:typedefTypeIR» typeIR_l) = true)))) (fun (_ : Unit) => (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$result_concat» typeIR_l typeIR_r⟩) (fun («exec:4» : SpecTec.typeIR) => (let «eval:1» : SpecTec.typeIR := «exec:4»; (.pure ((«eval:1» : SpecTec.typeIR)))))))))))) | none => .unmatch)))))


noncomputable def «$result_concat_clauses» (input0 : typeIR) (input1 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$result_concat:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$result_concat:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$result_concat:clause:2»  input0 input1), fun (_ : _root_.Unit) => («$result_concat:clause:3»  input0 input1), fun (_ : _root_.Unit) => («$result_concat:clause:4»  input0 input1), fun (_ : _root_.Unit) => («$result_concat:clause:5»  input0 input1), fun (_ : _root_.Unit) => («$result_concat:clause:6»  input0 input1)]


noncomputable def «$is_valid_bitslice:clause:0» (input0 : SpecTec.typeIR) (input1 : _root_.Nat) (input2 : _root_.Nat) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let n_lo : _root_.Nat := input1; (let n_hi : _root_.Nat := input2; (.bind (.guard (((«sub:typeIR:intTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$is_valid_bitslice:case_1:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.intTypeIR := «exec:1»; (let intTypeIR : SpecTec.intTypeIR := «eval:0»; (.bind (.guard (((SpecTec.intTypeIR.INT) : SpecTec.intTypeIR) = intTypeIR)) (fun (_ : Unit) => (.pure (((_root_.Decidable.decide (n_lo ≤ n_hi)) : _root_.Bool))))))) | none => .unmatch))))))


noncomputable def «$is_valid_bitslice:clause:1» (input0 : SpecTec.typeIR) (input1 : _root_.Nat) (input2 : _root_.Nat) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let n_lo : _root_.Nat := input1; (let n_hi : _root_.Nat := input2; (.bind (.guard (((«sub:typeIR:fixedIntTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$is_valid_bitslice:case_2:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : fixedIntTypeIR := «exec:1»; (match «eval:0» with | .«INT `< % `>» «exec:2» => (let w : _root_.Nat := «exec:2»; (let i : _root_.Int := (((_root_.Int.ofNat n_hi) - (_root_.Int.ofNat n_lo)) + (_root_.Int.ofNat (1 : _root_.Nat))); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ i)) = true))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Int) ≤ i))) (fun (_ : Unit) => (let w_slice : _root_.Nat := (_root_.Int.toNat i); (.pure (((((_root_.Decidable.decide (n_lo ≤ n_hi)) && (_root_.Decidable.decide (n_hi ≤ w))) && (_root_.Decidable.decide (w_slice ≤ w))) : _root_.Bool)))))))))))) | none => .unmatch))))))


noncomputable def «$is_valid_bitslice:clause:2» (input0 : SpecTec.typeIR) (input1 : _root_.Nat) (input2 : _root_.Nat) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let n_lo : _root_.Nat := input1; (let n_hi : _root_.Nat := input2; (.bind (.guard (((«sub:typeIR:fixedBitTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$is_valid_bitslice:case_3:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : fixedBitTypeIR := «exec:1»; (match «eval:0» with | .«BIT `< % `>» «exec:2» => (let w : _root_.Nat := «exec:2»; (let i : _root_.Int := (((_root_.Int.ofNat n_hi) - (_root_.Int.ofNat n_lo)) + (_root_.Int.ofNat (1 : _root_.Nat))); (.bind (.guard (((_root_.Decidable.decide ((0 : _root_.Int) ≤ i)) = true))) (fun (_ : Unit) => (.bind (.guard (((0 : _root_.Int) ≤ i))) (fun (_ : Unit) => (let w_slice : _root_.Nat := (_root_.Int.toNat i); (.pure (((((_root_.Decidable.decide (n_lo ≤ n_hi)) && (_root_.Decidable.decide (n_hi ≤ w))) && (_root_.Decidable.decide (w_slice ≤ w))) : _root_.Bool)))))))))))) | none => .unmatch))))))


noncomputable def «$is_valid_bitslice:clause:3» (input0 : SpecTec.typeIR) (input1 : _root_.Nat) (input2 : _root_.Nat) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (let n_lo : _root_.Nat := input1; (let n_hi : _root_.Nat := input2; (.bind (.guard (((«sub:typeIR:typedefTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$is_valid_bitslice:case_4:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : typedefTypeIR := «exec:1»; (match «eval:0» with | .TYPEDEF «exec:2» «exec:3» => (let _typeId : typeId := «exec:2»; (let typeIR : SpecTec.typeIR := «exec:3»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_valid_bitslice» typeIR n_lo n_hi⟩) (fun («exec:4» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:4»; (.pure ((«eval:1» : _root_.Bool)))))))))) | none => .unmatch))))))


noncomputable def «$is_valid_bitslice:clause:4» (input0 : typeIR) (input1 : _root_.Nat) (input2 : _root_.Nat) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (let _nat : _root_.Nat := input1; (let _nat' : _root_.Nat := input2; (.pure ((false : _root_.Bool))))))


noncomputable def «$is_valid_bitslice_clauses» (input0 : typeIR) (input1 : _root_.Nat) (input2 : _root_.Nat) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_valid_bitslice:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$is_valid_bitslice:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$is_valid_bitslice:clause:2»  input0 input1 input2), fun (_ : _root_.Unit) => («$is_valid_bitslice:clause:3»  input0 input1 input2), fun (_ : _root_.Unit) => («$is_valid_bitslice:clause:4»  input0 input1 input2)]


noncomputable def «$is_concrete_extern_object:clause:0» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$unroll_typeIR» typeIR⟩) (fun («exec:1» : SpecTec.typeIR) => (let «eval:0» : SpecTec.typeIR := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_concrete_extern_object'» «eval:0»⟩) (fun («exec:2» : _root_.Bool) => (let «eval:1» : _root_.Bool := «exec:2»; (.pure ((«eval:1» : _root_.Bool))))))))))


noncomputable def «$is_concrete_extern_object_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_concrete_extern_object:clause:0»  input0)]


noncomputable def «$subst_externMethodTypeDefEnv:clause:0» (input0 : externMethodTypeDefEnv) (input1 : externMethodTypeDefEnv) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externMethodTypeDefEnv_extern : externMethodTypeDefEnv := input0; (let «set<pair<callableId, externMethodTypeDefIR>>» : (set (pair callableId externMethodTypeDefIR)) := input1; (.bind (.guard (((set.«`{ % `}» ([] : (_root_.List (pair callableId externMethodTypeDefIR)))) : (set (pair callableId externMethodTypeDefIR))) = «set<pair<callableId, externMethodTypeDefIR>>»)) (fun (_ : Unit) => (.pure ((externMethodTypeDefEnv_extern : externMethodTypeDefEnv)))))))


noncomputable def «$subst_externMethodTypeDefEnv:clause:1» (input0 : externMethodTypeDefEnv) (input1 : externMethodTypeDefEnv) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externMethodTypeDefEnv_extern : externMethodTypeDefEnv := input0; (match input1 with | .«`{ % `}» «exec:1» => (let «pair<callableId, externMethodTypeDefIR>*» : (_root_.List (pair SpecTec.callableId SpecTec.externMethodTypeDefIR)) := «exec:1»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «pair<callableId, externMethodTypeDefIR>*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «pair<callableId, externMethodTypeDefIR>*» with | «exec:3» :: «exec:2» => (match «exec:3» with | .«% ':' %» «exec:4» «exec:5» => (let callableId_init_h : SpecTec.callableId := «exec:4»; (let externMethodTypeDefIR_init_h : SpecTec.externMethodTypeDefIR := «exec:5»; (let «eval:1» : (_root_.List (pair SpecTec.callableId SpecTec.externMethodTypeDefIR)) := «exec:2»; (.bind (.call ⟨((_root_.List SpecTec.callableId) × (_root_.List SpecTec.externMethodTypeDefIR)), SpecTecCall.«$subst_externMethodTypeDefEnv:case_2:pattern-iter:0» «eval:1»⟩) (fun («exec:6» : ((_root_.List SpecTec.callableId) × (_root_.List SpecTec.externMethodTypeDefIR))) => (let «callableId_init_t*» : (_root_.List SpecTec.callableId) := («exec:6»).1; (let «externMethodTypeDefIR_init_t*» : (_root_.List SpecTec.externMethodTypeDefIR) := («exec:6»).2; (match callableId_init_h with | .«% `( % `)» «exec:7» «exec:8» => (let nameIR_init_h : SpecTec.nameIR := «exec:7»; (let «_id*» : (_root_.List id) := «exec:8»; (.bind (.call ⟨(_root_.Option (SpecTec.callableId × SpecTec.externMethodTypeDefIR)), SpecTecCall.«$find_non_overloaded» SpecTec.externMethodTypeDefIR externMethodTypeDefEnv_extern nameIR_init_h⟩) (fun («exec:9» : (_root_.Option (SpecTec.callableId × SpecTec.externMethodTypeDefIR))) => (let «eval:2» : (_root_.Option (SpecTec.callableId × SpecTec.externMethodTypeDefIR)) := «exec:9»; (let «(callableId, externMethodTypeDefIR)?» : (_root_.Option (SpecTec.callableId × SpecTec.externMethodTypeDefIR)) := «eval:2»; (.bind (.guard (((_root_.Option.isSome «(callableId, externMethodTypeDefIR)?») = true))) (fun (_ : Unit) => (match «(callableId, externMethodTypeDefIR)?» with | some «exec:10» => (let callableId : SpecTec.callableId := («exec:10»).1; (let externMethodTypeDefIR_abstract : SpecTec.externMethodTypeDefIR := («exec:10»).2; (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := externMethodTypeDefIR_abstract; (.bind (.guard (((«exec:match:externMethodTypeDefIR:EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» externMethodTypeDefIR) = true))) (fun (_ : Unit) => (match externMethodTypeDefIR with | .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» «exec:11» «exec:12» «exec:13» «exec:14» «exec:15» => (let nameIR : SpecTec.nameIR := «exec:11»; (let «typeId_expl*» : (_root_.List typeId) := «exec:12»; (let «typeId_impl*» : (_root_.List typeId) := «exec:13»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:14»; (let typeIR_ret : typeIR := «exec:15»; (let externMethodTypeDefIR_concrete : SpecTec.externMethodTypeDefIR := ((SpecTec.externMethodTypeDefIR.«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» nameIR «typeId_expl*» «typeId_impl*» «parameterIR*» typeIR_ret) : SpecTec.externMethodTypeDefIR); (.bind (.call ⟨_root_.Unit, SpecTecCall.ExternMethodTypeDef_alpha externMethodTypeDefIR_concrete externMethodTypeDefIR_init_h⟩) (fun («exec:16» : _root_.Unit) => (.bind (.call ⟨(map SpecTec.callableId SpecTec.externMethodTypeDefIR), SpecTecCall.«$update_map» SpecTec.callableId SpecTec.externMethodTypeDefIR externMethodTypeDefEnv_extern callableId externMethodTypeDefIR_concrete⟩) (fun («exec:17» : (map SpecTec.callableId SpecTec.externMethodTypeDefIR)) => (let «eval:3» : (map SpecTec.callableId SpecTec.externMethodTypeDefIR) := «exec:17»; (let externMethodTypeDefEnv_extern_subst : externMethodTypeDefEnv := «eval:3»; (.bind (.call ⟨(_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR)), SpecTecCall.«$subst_externMethodTypeDefEnv:case_2:iter:4» «callableId_init_t*» «externMethodTypeDefIR_init_t*»⟩) (fun («exec:18» : (_root_.List (pair callTargetId SpecTec.externMethodTypeDefIR))) => (let «eval:5» : (_root_.List (pair SpecTec.callableId SpecTec.externMethodTypeDefIR)) := «exec:18»; (.bind (.call ⟨externMethodTypeDefEnv, SpecTecCall.«$subst_externMethodTypeDefEnv» externMethodTypeDefEnv_extern_subst ((set.«`{ % `}» «eval:5») : (set (pair SpecTec.callableId SpecTec.externMethodTypeDefIR)))⟩) (fun («exec:19» : externMethodTypeDefEnv) => (let «eval:6» : externMethodTypeDefEnv := «exec:19»; (.pure ((«eval:6» : externMethodTypeDefEnv))))))))))))))))))))) | _ => .unmatch)))))) | none => .unmatch)))))))))))))))))) | [] => .unmatch))))))


noncomputable def «$subst_externMethodTypeDefEnv_clauses» (input0 : externMethodTypeDefEnv) (input1 : externMethodTypeDefEnv) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_externMethodTypeDefEnv:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_externMethodTypeDefEnv:clause:1»  input0 input1)]


noncomputable def «$is_table_application:clause:0» (input0 : SpecTec.typedExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typedExpressionIR : SpecTec.typedExpressionIR := input0; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$type_of_typedExpressionIR» typedExpressionIR⟩) (fun («exec:1» : SpecTec.typeIR) => (let «eval:0» : SpecTec.typeIR := «exec:1»; (let typeIR : SpecTec.typeIR := «eval:0»; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$unroll_typeIR» typeIR⟩) (fun («exec:2» : SpecTec.typeIR) => (let «eval:1» : SpecTec.typeIR := «exec:2»; (let typeIR_unroll : SpecTec.typeIR := «eval:1»; (.pure (((«sub:typeIR:tableMetadataStructTypeIR» typeIR_unroll) : _root_.Bool))))))))))))


noncomputable def «$is_table_application_clauses» (input0 : typedExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_table_application:clause:0»  input0)]


noncomputable def «Call_action_partial_ok:rule:iter:2:clause:0» (input0 : (_root_.List typedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «Call_action_partial_ok:rule:iter:2:clause:1» (input0 : (_root_.List typedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typedExpressionIR_sub : typedExpressionIR := «exec:2»; (let «tail:0» : (_root_.List typedExpressionIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_table_application» typedExpressionIR_sub⟩) (fun («exec:3» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Call_action_partial_ok:rule:iter:2» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure ((((!«eval:3») :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «Call_action_partial_ok:rule:iter:2_clauses» (input0 : (_root_.List typedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_action_partial_ok:rule:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Call_action_partial_ok:rule:iter:2:clause:1»  input0)]


noncomputable def «Call_action_default_ok:rule:iter:2:clause:0» (input0 : (_root_.List typedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «Call_action_default_ok:rule:iter:2:clause:1» (input0 : (_root_.List typedExpressionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typedExpressionIR_sub : typedExpressionIR := «exec:2»; (let «tail:0» : (_root_.List typedExpressionIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_table_application» typedExpressionIR_sub⟩) (fun («exec:3» : _root_.Bool) => (let «eval:3» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Call_action_default_ok:rule:iter:2» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure ((((!«eval:3») :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «Call_action_default_ok:rule:iter:2_clauses» (input0 : (_root_.List typedExpressionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_action_default_ok:rule:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Call_action_default_ok:rule:iter:2:clause:1»  input0)]


noncomputable def «$resolve_inference':clause:0» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$unroll_typeIR» typeIR⟩) (fun («exec:1» : SpecTec.typeIR) => (let «eval:0» : SpecTec.typeIR := «exec:1»; (let typeIR' : SpecTec.typeIR := «eval:0»; (.bind (.guard (((«sub:typeIR:sequenceTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$resolve_inference':case_1:downcast:1» typeIR') with | some «exec:2» => (let «eval:1» : SpecTec.sequenceTypeIR := «exec:2»; (let sequenceTypeIR : SpecTec.sequenceTypeIR := «eval:1»; (.bind (.guard (((«exec:match:sequenceTypeIR:SEQ `< % `>» sequenceTypeIR) = true))) (fun (_ : Unit) => (match sequenceTypeIR with | .«SEQ `< % `>» «exec:3» => (let «typeIR_arg*» : (_root_.List SpecTec.typeIR) := «exec:3»; (let typeIR_resolved : SpecTec.typeIR := ((SpecTec.typeIR.«TUPLE `< % `>» «typeIR_arg*») : SpecTec.typeIR); (.pure ((typeIR_resolved : SpecTec.typeIR))))) | _ => .unmatch))))) | none => .unmatch))))))))


noncomputable def «$resolve_inference':clause:1» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.pure ((typeIR : SpecTec.typeIR))))


noncomputable def «$resolve_inference'_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$resolve_inference':clause:0»  input0), fun (_ : _root_.Unit) => («$resolve_inference':clause:1»  input0)]


noncomputable def «$resolve_inference:case_1:iter:2:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «$resolve_inference:case_1:iter:2:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$resolve_inference'» typeIR⟩) (fun («exec:3» : SpecTec.typeIR) => (let «eval:3» : SpecTec.typeIR := «exec:3»; (let typeIR_resolved : SpecTec.typeIR := «eval:3»; (.bind (.call ⟨(_root_.List SpecTec.typeIR), SpecTecCall.«$resolve_inference:case_1:iter:2» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.typeIR)) => (let «tail:1» : (_root_.List SpecTec.typeIR) := «exec:4»; (.pure (((typeIR_resolved :: «tail:1») : (_root_.List SpecTec.typeIR))))))))))))) | [] => .unmatch)


noncomputable def «$resolve_inference:case_1:iter:2_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$resolve_inference:case_1:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$resolve_inference:case_1:iter:2:clause:1»  input0)]


noncomputable def «$resolve_inference:clause:0» (input0 : inference) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «eval:1» : (_root_.List (pair typeId typeIR)) := «exec:1»; (.bind (.call ⟨((_root_.List typeIR) × (_root_.List typeId)), SpecTecCall.«$resolve_inference:case_1:pattern-iter:0» «eval:1»⟩) (fun («exec:2» : ((_root_.List typeIR) × (_root_.List typeId))) => (let «typeIR*» : (_root_.List typeIR) := («exec:2»).1; (let «typeId*» : (_root_.List typeId) := («exec:2»).2; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$resolve_inference:case_1:iter:2» «typeIR*»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «typeIR_resolved*» : (_root_.List typeIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«$resolve_inference:case_1:iter:4» «typeIR_resolved*» «typeId*»⟩) (fun («exec:4» : (_root_.List (pair _root_.String typeIR))) => (let «eval:5» : (_root_.List (pair typeId typeIR)) := «exec:4»; (.pure ((((set.«`{ % `}» «eval:5») : (set (pair typeId typeIR))) : inference)))))))))))))))


noncomputable def «$resolve_inference_clauses» (input0 : inference) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$resolve_inference:clause:0»  input0)]


noncomputable def «$merge_constraint':clause:0» (input0 : SpecTec.constraint) (input1 : SpecTec.constraint) (input2 : (_root_.List typeId)) (input3 : SpecTec.constraint) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let constraint_pre : SpecTec.constraint := input0; (let constraint_post : SpecTec.constraint := input1; (let «typeId*» : (_root_.List typeId) := input2; (let constraint : SpecTec.constraint := input3; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeId*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((constraint : SpecTec.constraint)))))))))


noncomputable def «$merge_constraint':clause:1» (input0 : SpecTec.constraint) (input1 : SpecTec.constraint) (input2 : (_root_.List typeId)) (input3 : SpecTec.constraint) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let constraint_pre : SpecTec.constraint := input0; (let constraint_post : SpecTec.constraint := input1; (let «typeId*» : (_root_.List typeId) := input2; (let constraint : SpecTec.constraint := input3; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeId*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «typeId*» with | «exec:2» :: «exec:1» => (let typeId_h : typeId := «exec:2»; (let «typeId_t*» : (_root_.List typeId) := «exec:1»; (.bind (.call ⟨(_root_.Option infer), SpecTecCall.«$find_map» typeId infer constraint_pre typeId_h⟩) (fun («exec:3» : (_root_.Option infer)) => (let «eval:0» : (_root_.Option infer) := «exec:3»; (match «eval:0» with | some «exec:4» => (match «exec:4» with | .UNKNOWN  => (.bind (.call ⟨(_root_.Option infer), SpecTecCall.«$find_map» typeId infer constraint_post typeId_h⟩) (fun («exec:5» : (_root_.Option infer)) => (let «eval:1» : (_root_.Option infer) := «exec:5»; (match «eval:1» with | some «exec:6» => (match «exec:6» with | .UNKNOWN  => (.bind (.call ⟨(map typeId infer), SpecTecCall.«$update_map» typeId infer constraint typeId_h ((infer.UNKNOWN) : infer)⟩) (fun («exec:7» : (map typeId infer)) => (let «eval:2» : (map typeId infer) := «exec:7»; (let constraint_updated : SpecTec.constraint := «eval:2»; (.bind (.call ⟨SpecTec.constraint, SpecTecCall.«$merge_constraint'» constraint_pre constraint_post «typeId_t*» constraint_updated⟩) (fun («exec:8» : SpecTec.constraint) => (let «eval:3» : SpecTec.constraint := «exec:8»; (.pure ((«eval:3» : SpecTec.constraint)))))))))) | _ => .unmatch) | none => .unmatch)))) | _ => .unmatch) | none => .unmatch)))))) | [] => .unmatch)))))))


noncomputable def «$merge_constraint':clause:2» (input0 : SpecTec.constraint) (input1 : SpecTec.constraint) (input2 : (_root_.List typeId)) (input3 : SpecTec.constraint) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let constraint_pre : SpecTec.constraint := input0; (let constraint_post : SpecTec.constraint := input1; (let «typeId*» : (_root_.List typeId) := input2; (let constraint : SpecTec.constraint := input3; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «typeId*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «typeId*» with | «exec:2» :: «exec:1» => (let typeId_h : typeId := «exec:2»; (let «typeId_t*» : (_root_.List typeId) := «exec:1»; (.bind (.call ⟨(_root_.Option SpecTec.infer), SpecTecCall.«$find_map» typeId SpecTec.infer constraint_pre typeId_h⟩) (fun («exec:3» : (_root_.Option SpecTec.infer)) => (let «eval:0» : (_root_.Option SpecTec.infer) := «exec:3»; (match «eval:0» with | some «exec:4» => (match «exec:4» with | .UNKNOWN  => (.bind (.call ⟨(_root_.Option SpecTec.infer), SpecTecCall.«$find_map» typeId SpecTec.infer constraint_post typeId_h⟩) (fun («exec:5» : (_root_.Option SpecTec.infer)) => (let «eval:1» : (_root_.Option SpecTec.infer) := «exec:5»; (let infer'? : (_root_.Option SpecTec.infer) := «eval:1»; (.bind (.guard (((_root_.Option.isSome infer'?) = true))) (fun (_ : Unit) => (match infer'? with | some «exec:6» => (let infer : SpecTec.infer := «exec:6»; (.bind (.guard (((«exec:match:infer:KNOWN AS %» infer) = true))) (fun (_ : Unit) => (match infer with | .«KNOWN AS %» «exec:7» => (let typeIR_post : typeIR := «exec:7»; (.bind (.call ⟨(map typeId SpecTec.infer), SpecTecCall.«$update_map» typeId SpecTec.infer constraint typeId_h ((SpecTec.infer.«KNOWN AS %» typeIR_post) : SpecTec.infer)⟩) (fun («exec:8» : (map typeId SpecTec.infer)) => (let «eval:2» : (map typeId SpecTec.infer) := «exec:8»; (let constraint_updated : SpecTec.constraint := «eval:2»; (.bind (.call ⟨SpecTec.constraint, SpecTecCall.«$merge_constraint'» constraint_pre constraint_post «typeId_t*» constraint_updated⟩) (fun («exec:9» : SpecTec.constraint) => (let «eval:3» : SpecTec.constraint := «exec:9»; (.pure ((«eval:3» : SpecTec.constraint))))))))))) | _ => .unmatch)))) | none => .unmatch))))))) | _ => .unmatch) | none => .unmatch)))))) | [] => .unmatch)))))))

end SpecTec
