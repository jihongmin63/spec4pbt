import SpecTecDecl0210

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «InstDecl_non_objectInitializer_ok:rule:iter:1:clause:1» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeId_inserted : typeId := «exec:2»; (let «tail:0» : (_root_.List typeId) := «exec:1»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«InstDecl_non_objectInitializer_ok:rule:iter:1» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((((typeIR._NAME typeId_inserted) : typeIR) :: «tail:1») : (_root_.List typeIR))))))))) | [] => .unmatch)


noncomputable def «InstDecl_non_objectInitializer_ok:rule:iter:1_clauses» (input0 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («InstDecl_non_objectInitializer_ok:rule:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («InstDecl_non_objectInitializer_ok:rule:iter:1:clause:1»  input0)]


noncomputable def «$subst_externMethodTypeDefEnv:case_2:pattern-iter:0:clause:0» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List callableId)), ([] : (_root_.List externMethodTypeDefIR))) : ((_root_.List callableId) × (_root_.List externMethodTypeDefIR))))) | _ :: _ => .unmatch)


noncomputable def «$subst_externMethodTypeDefEnv:case_2:pattern-iter:0:clause:1» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let callableId_init_t : callableId := «exec:3»; (let externMethodTypeDefIR_init_t : externMethodTypeDefIR := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId externMethodTypeDefIR)) := «exec:1»; (.bind (.call ⟨((_root_.List callableId) × (_root_.List externMethodTypeDefIR)), SpecTecCall.«$subst_externMethodTypeDefEnv:case_2:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List callableId) × (_root_.List externMethodTypeDefIR))) => (let «pattern-tail:1» : (_root_.List callableId) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List externMethodTypeDefIR) := («exec:5»).2; (.pure ((((callableId_init_t :: «pattern-tail:1»), (externMethodTypeDefIR_init_t :: «pattern-tail:2»)) : ((_root_.List callableId) × (_root_.List externMethodTypeDefIR))))))))))))) | [] => .unmatch)


noncomputable def «$subst_externMethodTypeDefEnv:case_2:pattern-iter:0_clauses» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_externMethodTypeDefEnv:case_2:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$subst_externMethodTypeDefEnv:case_2:pattern-iter:0:clause:1»  input0)]


noncomputable def «$subst_externMethodTypeDefEnv:case_2:iter:4:clause:0» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId externMethodTypeDefIR))) : (_root_.List (pair callTargetId externMethodTypeDefIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$subst_externMethodTypeDefEnv:case_2:iter:4:clause:1» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let callableId_init_t : callableId := «exec:2»; (let «tail:0» : (_root_.List callableId) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let externMethodTypeDefIR_init_t : externMethodTypeDefIR := «exec:4»; (let «tail:1» : (_root_.List externMethodTypeDefIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId externMethodTypeDefIR)), SpecTecCall.«$subst_externMethodTypeDefEnv:case_2:iter:4» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId externMethodTypeDefIR))) => (let «tail:2» : (_root_.List (pair callTargetId externMethodTypeDefIR)) := «exec:5»; (.pure (((((pair.«% ':' %» callableId_init_t externMethodTypeDefIR_init_t) : (pair callableId externMethodTypeDefIR)) :: «tail:2») : (_root_.List (pair callTargetId externMethodTypeDefIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$subst_externMethodTypeDefEnv:case_2:iter:4_clauses» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_externMethodTypeDefEnv:case_2:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_externMethodTypeDefEnv:case_2:iter:4:clause:1»  input0 input1)]


noncomputable def «InstDecl_objectInitializer_ok:rule:iter:1:clause:0» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeIR)) : (_root_.List typeIR)))) | _ :: _ => .unmatch)


noncomputable def «InstDecl_objectInitializer_ok:rule:iter:1:clause:1» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeId_inserted : typeId := «exec:2»; (let «tail:0» : (_root_.List typeId) := «exec:1»; (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«InstDecl_objectInitializer_ok:rule:iter:1» «tail:0»⟩) (fun («exec:3» : (_root_.List typeIR)) => (let «tail:1» : (_root_.List typeIR) := «exec:3»; (.pure (((((typeIR._NAME typeId_inserted) : typeIR) :: «tail:1») : (_root_.List typeIR))))))))) | [] => .unmatch)


noncomputable def «InstDecl_objectInitializer_ok:rule:iter:1_clauses» (input0 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («InstDecl_objectInitializer_ok:rule:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («InstDecl_objectInitializer_ok:rule:iter:1:clause:1»  input0)]


noncomputable def «$constructorTypeDef_of_externConstructorPrototypeIR:clause:0» (input0 : SpecTec.typeParameterListIR) (input1 : SpecTec.typeIR) (input2 : externConstructorPrototypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeParameterListIR_expl : SpecTec.typeParameterListIR := input0; (let typeIR : SpecTec.typeIR := input1; (match input2 with | .«% % `< ',' % `> `( % `) ';'» «exec:1» «exec:2» «exec:3» «exec:4» => (let _annotationList : annotationList := «exec:1»; (let nameIR : SpecTec.nameIR := «exec:2»; (let typeParameterListIR_impl : SpecTec.typeParameterListIR := «exec:3»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:4»; (let typeParameterListIR : SpecTec.typeParameterListIR := (typeParameterListIR_expl ++ typeParameterListIR_impl); (let constructorTypeDefIR : SpecTec.constructorTypeDefIR := ((SpecTec.constructorTypeDefIR.«CONSTRUCTOR `< % ',' % `> `( % `) ':' %» typeParameterListIR_expl typeParameterListIR_impl «parameterIR*» typeIR) : SpecTec.constructorTypeDefIR); (.pure ((constructorTypeDefIR : SpecTec.constructorTypeDefIR))))))))))))


noncomputable def «$constructorTypeDef_of_externConstructorPrototypeIR_clauses» (input0 : typeParameterListIR) (input1 : typeIR) (input2 : externConstructorPrototypeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$constructorTypeDef_of_externConstructorPrototypeIR:clause:0»  input0 input1 input2)]


noncomputable def «Decl_ok:externObjectDeclaration:iter:17:clause:0» (input0 : (_root_.List typeId)) (input1 : typeIR) (input2 : (_root_.List externConstructorPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «typeId_expl*» : (_root_.List typeId) := input0; (let typeIR_extern : typeIR := input1; (match input2 with | [] => (.pure ((([] : (_root_.List constructorTypeDefIR)) : (_root_.List constructorTypeDefIR)))) | _ :: _ => .unmatch)))


noncomputable def «Decl_ok:externObjectDeclaration:iter:17:clause:1» (input0 : (_root_.List typeId)) (input1 : typeIR) (input2 : (_root_.List SpecTec.externConstructorPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «typeId_expl*» : (_root_.List typeId) := input0; (let typeIR_extern : typeIR := input1; (match input2 with | «exec:2» :: «exec:1» => (let externConstructorPrototypeIR : SpecTec.externConstructorPrototypeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.externConstructorPrototypeIR) := «exec:1»; (.bind (.call ⟨SpecTec.constructorTypeDefIR, SpecTecCall.«$constructorTypeDef_of_externConstructorPrototypeIR» «typeId_expl*» typeIR_extern externConstructorPrototypeIR⟩) (fun («exec:3» : SpecTec.constructorTypeDefIR) => (let «eval:18» : SpecTec.constructorTypeDefIR := «exec:3»; (let constructorTypeDefIR : SpecTec.constructorTypeDefIR := «eval:18»; (.bind (.call ⟨(_root_.List SpecTec.constructorTypeDefIR), SpecTecCall.«Decl_ok:externObjectDeclaration:iter:17» «typeId_expl*» typeIR_extern «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.constructorTypeDefIR)) => (let «tail:1» : (_root_.List SpecTec.constructorTypeDefIR) := «exec:4»; (.pure (((constructorTypeDefIR :: «tail:1») : (_root_.List SpecTec.constructorTypeDefIR))))))))))))) | [] => .unmatch)))


noncomputable def «Decl_ok:externObjectDeclaration:iter:17_clauses» (input0 : (_root_.List typeId)) (input1 : typeIR) (input2 : (_root_.List externConstructorPrototypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_ok:externObjectDeclaration:iter:17:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Decl_ok:externObjectDeclaration:iter:17:clause:1»  input0 input1 input2)]


noncomputable def «$compat_mask:clause:0» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .INT  => (match input1 with | .INT  => (.bind (.guard ((0 : _root_.Nat) = («$compat_mask:matches:0:row» ((typeIR.INT) : typeIR) ((typeIR.INT) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch) | _ => .unmatch)


noncomputable def «$compat_mask:clause:1» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let w_l : _root_.Nat := «exec:1»; (match input1 with | .«INT `< % `>» «exec:2» => (let w_r : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_mask:matches:1:row» ((typeIR.«INT `< % `>» w_l) : typeIR) ((typeIR.«INT `< % `>» w_r) : typeIR)))) (fun (_ : Unit) => (.pure (((_root_.Decidable.decide (w_l = w_r)) : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_mask:clause:2» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let w_l : _root_.Nat := «exec:1»; (match input1 with | .«BIT `< % `>» «exec:2» => (let w_r : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_mask:matches:2:row» ((typeIR.«BIT `< % `>» w_l) : typeIR) ((typeIR.«BIT `< % `>» w_r) : typeIR)))) (fun (_ : Unit) => (.pure (((_root_.Decidable.decide (w_l = w_r)) : _root_.Bool)))))) | _ => .unmatch)) | _ => .unmatch)


noncomputable def «$compat_mask:clause:3» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR_l : typeIR := «exec:2»; (let typeIR_r : typeIR := input1; (.bind (.guard ((0 : _root_.Nat) = («$compat_mask:matches:3:row» ((typeIR.TYPEDEF _typeId typeIR_l) : typeIR) typeIR_r))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_mask» typeIR_l typeIR_r⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool))))))))))) | _ => .unmatch)


noncomputable def «$compat_mask:clause:4» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR_l : typeIR := input0; (match input1 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR_r : typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_mask:matches:4:row» typeIR_l ((typeIR.TYPEDEF _typeId typeIR_r) : typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_mask» typeIR_l typeIR_r⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch))


noncomputable def «$compat_mask:clause:5» (input0 : typeIR) (input1 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (let _typeIR' : typeIR := input1; (.bind (.guard ((0 : _root_.Nat) = («$compat_mask:matches:5:row» _typeIR _typeIR'))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))


noncomputable def «$compat_mask_clauses» (input0 : typeIR) (input1 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_mask:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$compat_mask:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$compat_mask:clause:2»  input0 input1), fun (_ : _root_.Unit) => («$compat_mask:clause:3»  input0 input1), fun (_ : _root_.Unit) => («$compat_mask:clause:4»  input0 input1), fun (_ : _root_.Unit) => («$compat_mask:clause:5»  input0 input1)]


noncomputable def «$compat_table_exact_optional_key:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .BOOL  => (.bind (.guard ((0 : _root_.Nat) = («$compat_table_exact_optional_key:matches:0:row» ((typeIR.BOOL) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$compat_table_exact_optional_key:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .ERROR  => (.bind (.guard ((0 : _root_.Nat) = («$compat_table_exact_optional_key:matches:1:row» ((typeIR.ERROR) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$compat_table_exact_optional_key:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let integerTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$compat_table_exact_optional_key:matches:2:row» integerTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$compat_table_exact_optional_key:clause:3» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_table_exact_optional_key:matches:3:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_table_exact_optional_key» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$compat_table_exact_optional_key:clause:4» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPE «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_table_exact_optional_key:matches:4:row» ((SpecTec.typeIR.TYPE _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_table_exact_optional_key» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$compat_table_exact_optional_key:clause:5» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«ENUM % `{ % `}» «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let «_nameIR*» : (_root_.List nameIR) := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_table_exact_optional_key:matches:5:row» ((typeIR.«ENUM % `{ % `}» _typeId «_nameIR*») : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))) | _ => .unmatch)


noncomputable def «$compat_table_exact_optional_key:clause:6» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«ENUM % `< % `> `{ % `}» «exec:1» «exec:2» «exec:3» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (let «_valueFieldIR*» : (_root_.List valueFieldIR) := «exec:3»; (.bind (.guard ((0 : _root_.Nat) = («$compat_table_exact_optional_key:matches:6:row» ((SpecTec.typeIR.«ENUM % `< % `> `{ % `}» _typeId typeIR «_valueFieldIR*») : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_table_exact_optional_key» typeIR⟩) (fun («exec:4» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:4»; (.pure ((«eval:0» : _root_.Bool))))))))))) | _ => .unmatch)


noncomputable def «$compat_table_exact_optional_key:clause:7» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$compat_table_exact_optional_key:matches:7:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$compat_table_exact_optional_key_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_table_exact_optional_key:clause:0»  input0), fun (_ : _root_.Unit) => («$compat_table_exact_optional_key:clause:1»  input0), fun (_ : _root_.Unit) => («$compat_table_exact_optional_key:clause:2»  input0), fun (_ : _root_.Unit) => («$compat_table_exact_optional_key:clause:3»  input0), fun (_ : _root_.Unit) => («$compat_table_exact_optional_key:clause:4»  input0), fun (_ : _root_.Unit) => («$compat_table_exact_optional_key:clause:5»  input0), fun (_ : _root_.Unit) => («$compat_table_exact_optional_key:clause:6»  input0), fun (_ : _root_.Unit) => («$compat_table_exact_optional_key:clause:7»  input0)]

end SpecTec
