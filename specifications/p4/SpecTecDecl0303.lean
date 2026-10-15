import SpecTecDecl0302

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$sizeof_maxSizeInBits:clause:0» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.call ⟨_root_.Nat, SpecTecCall.«$sizeof_maxSizeInBits'» typeIR⟩) (fun («exec:1» : _root_.Nat) => (let «eval:0» : _root_.Nat := «exec:1»; (.pure ((((value.D (_root_.Int.ofNat «eval:0»)) : value) : value)))))))


noncomputable def «$sizeof_maxSizeInBits_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits:clause:0»  input0)]


noncomputable def «$sizeof_maxSizeInBytes:clause:0» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.call ⟨_root_.Nat, SpecTecCall.«$sizeof_maxSizeInBits'» typeIR⟩) (fun («exec:1» : _root_.Nat) => (let «eval:0» : _root_.Nat := «exec:1»; (let n_size : _root_.Nat := «eval:0»; (.bind (SpecTecExecution.require (((8 : _root_.Nat) ≠ (0 : _root_.Nat))) "division by zero") (fun (_ : Unit) => (.pure ((((value.D (_root_.Int.ofNat (n_size / (8 : _root_.Nat)))) : value) : value))))))))))


noncomputable def «$sizeof_maxSizeInBytes_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$sizeof_maxSizeInBytes:clause:0»  input0)]


noncomputable def «$sizeof:clause:0» (input0 : SpecTec.typeIR) (input1 : id) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let t : _root_.String := input1; (.bind (.guard ("minSizeInBits" = t)) (fun (_ : Unit) => (.bind (.call ⟨value, SpecTecCall.«$sizeof_minSizeInBits» typeIR⟩) (fun («exec:1» : value) => (let «eval:0» : value := «exec:1»; (.pure ((«eval:0» : value))))))))))


noncomputable def «$sizeof:clause:1» (input0 : SpecTec.typeIR) (input1 : id) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let t : _root_.String := input1; (.bind (.guard ("minSizeInBytes" = t)) (fun (_ : Unit) => (.bind (.call ⟨value, SpecTecCall.«$sizeof_minSizeInBytes» typeIR⟩) (fun («exec:1» : value) => (let «eval:0» : value := «exec:1»; (.pure ((«eval:0» : value))))))))))


noncomputable def «$sizeof:clause:2» (input0 : SpecTec.typeIR) (input1 : id) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let t : _root_.String := input1; (.bind (.guard ("maxSizeInBits" = t)) (fun (_ : Unit) => (.bind (.call ⟨value, SpecTecCall.«$sizeof_maxSizeInBits» typeIR⟩) (fun («exec:1» : value) => (let «eval:0» : value := «exec:1»; (.pure ((«eval:0» : value))))))))))


noncomputable def «$sizeof:clause:3» (input0 : SpecTec.typeIR) (input1 : id) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (let t : _root_.String := input1; (.bind (.guard ("maxSizeInBytes" = t)) (fun (_ : Unit) => (.bind (.call ⟨value, SpecTecCall.«$sizeof_maxSizeInBytes» typeIR⟩) (fun («exec:1» : value) => (let «eval:0» : value := «exec:1»; (.pure ((«eval:0» : value))))))))))


noncomputable def «$sizeof_clauses» (input0 : typeIR) (input1 : id) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$sizeof:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$sizeof:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$sizeof:clause:2»  input0 input1), fun (_ : _root_.Unit) => («$sizeof:clause:3»  input0 input1)]


noncomputable def «$lift_typeIR:clause:0» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:baseTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$lift_typeIR:case_1:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.baseTypeIR := «exec:1»; (let baseTypeIR : SpecTec.baseTypeIR := «eval:0»; (.bind (.call ⟨baseType, SpecTecCall.«$lift_baseTypeIR» baseTypeIR⟩) (fun («exec:2» : baseType) => (let «eval:1» : baseType := «exec:2»; (.pure (((«cast:baseType:type» «eval:1») : type)))))))) | none => .unmatch))))


noncomputable def «$lift_typeIR:clause:1» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:nameTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$lift_typeIR:case_2:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.nameTypeIR := «exec:1»; (let nameTypeIR : SpecTec.nameTypeIR := «eval:0»; (.bind (.call ⟨namedType, SpecTecCall.«$lift_nameTypeIR» nameTypeIR⟩) (fun («exec:2» : namedType) => (let «eval:1» : namedType := «exec:2»; (.pure (((«cast:namedType:type» «eval:1») : type)))))))) | none => .unmatch))))


noncomputable def «$lift_typeIR:clause:2» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:aliasTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$lift_typeIR:case_3:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.aliasTypeIR := «exec:1»; (let aliasTypeIR : SpecTec.aliasTypeIR := «eval:0»; (.bind (.call ⟨type, SpecTecCall.«$lift_aliasTypeIR» aliasTypeIR⟩) (fun («exec:2» : type) => (let «eval:1» : type := «exec:2»; (.pure ((«eval:1» : type)))))))) | none => .unmatch))))


noncomputable def «$lift_typeIR:clause:3» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:dataTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$lift_typeIR:case_4:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.dataTypeIR := «exec:1»; (let dataTypeIR : SpecTec.dataTypeIR := «eval:0»; (.bind (.call ⟨type, SpecTecCall.«$lift_dataTypeIR» dataTypeIR⟩) (fun («exec:2» : type) => (let «eval:1» : type := «exec:2»; (.pure ((«eval:1» : type)))))))) | none => .unmatch))))


noncomputable def «$lift_typeIR:clause:4» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.call ⟨type, SpecTecCall.«$sink» type⟩) (fun («exec:1» : type) => (let «eval:0» : type := «exec:1»; (.pure ((«eval:0» : type)))))))


noncomputable def «$lift_typeIR_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_typeIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_typeIR:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_typeIR:clause:2»  input0), fun (_ : _root_.Unit) => («$lift_typeIR:clause:3»  input0), fun (_ : _root_.Unit) => («$lift_typeIR:clause:4»  input0)]


noncomputable def «$lift_typeArgumentListIR:clause:0» (input0 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «typeArgumentIR*» : (_root_.List typeArgumentIR) := input0; (.bind (.call ⟨(_root_.List typeArgument), SpecTecCall.«$lift_typeArgumentListIR:case_1:iter:0» «typeArgumentIR*»⟩) (fun («exec:1» : (_root_.List typeArgument)) => (let «typeArgument*» : (_root_.List typeArgument) := «exec:1»; (.bind (.call ⟨SpecTec.typeArgumentList, SpecTecCall.«$unflatten_typeArgumentList» «typeArgument*»⟩) (fun («exec:2» : SpecTec.typeArgumentList) => (let «eval:2» : SpecTec.typeArgumentList := «exec:2»; (let typeArgumentList : SpecTec.typeArgumentList := «eval:2»; (.pure ((typeArgumentList : SpecTec.typeArgumentList)))))))))))


noncomputable def «$lift_typeArgumentListIR_clauses» (input0 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_typeArgumentListIR:clause:0»  input0)]


noncomputable def «$lift_typeArgumentListIR:case_1:iter:0:clause:0» (input0 : (_root_.List typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typeArgument)) : (_root_.List typeArgument)))) | _ :: _ => .unmatch)


noncomputable def «$lift_typeArgumentListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (.bind (.call ⟨SpecTec.typeArgument, SpecTecCall.«$lift_typeArgumentIR» typeArgumentIR⟩) (fun («exec:3» : SpecTec.typeArgument) => (let «eval:1» : SpecTec.typeArgument := «exec:3»; (let typeArgument : SpecTec.typeArgument := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.typeArgument), SpecTecCall.«$lift_typeArgumentListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.typeArgument)) => (let «tail:1» : (_root_.List SpecTec.typeArgument) := «exec:4»; (.pure (((typeArgument :: «tail:1») : (_root_.List SpecTec.typeArgument))))))))))))) | [] => .unmatch)


noncomputable def «$lift_typeArgumentListIR:case_1:iter:0_clauses» (input0 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_typeArgumentListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_typeArgumentListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_typeArgumentIR:clause:0» (input0 : typeArgumentIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.call ⟨realTypeArgument, SpecTecCall.«$lift_typeArgumentIR_as_realTypeArgument» typeIR⟩) (fun («exec:1» : realTypeArgument) => (let «eval:0» : realTypeArgument := «exec:1»; (.pure (((«cast:realTypeArgument:typeArgument» «eval:0») : typeArgument)))))))


noncomputable def «$lift_typeArgumentIR_clauses» (input0 : typeArgumentIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_typeArgumentIR:clause:0»  input0)]


noncomputable def «$lift_dataTypeIR:clause:0» (input0 : SpecTec.dataTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let dataTypeIR : SpecTec.dataTypeIR := input0; (.bind (.guard (((«sub:dataTypeIR:listTypeIR» dataTypeIR) = true))) (fun (_ : Unit) => (match («$lift_dataTypeIR:case_1:downcast:0» dataTypeIR) with | some «exec:1» => (let «eval:0» : listTypeIR := «exec:1»; (match «eval:0» with | .«LIST `< % `>» «exec:2» => (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.call ⟨SpecTec.typeArgument, SpecTecCall.«$lift_typeArgumentIR» typeIR⟩) (fun («exec:3» : SpecTec.typeArgument) => (let «eval:1» : SpecTec.typeArgument := «exec:3»; (let typeArgument : SpecTec.typeArgument := «eval:1»; (.pure ((((type.«LIST `< % `>» typeArgument) : type) : type)))))))))) | none => .unmatch))))


noncomputable def «$lift_dataTypeIR:clause:1» (input0 : SpecTec.dataTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let dataTypeIR : SpecTec.dataTypeIR := input0; (.bind (.guard (((«sub:dataTypeIR:tupleTypeIR» dataTypeIR) = true))) (fun (_ : Unit) => (match («$lift_dataTypeIR:case_2:downcast:0» dataTypeIR) with | some «exec:1» => (let «eval:0» : tupleTypeIR := «exec:1»; (match «eval:0» with | .«TUPLE `< % `>» «exec:2» => (let «typeIR*» : (_root_.List typeIR) := «exec:2»; (.bind (.call ⟨SpecTec.typeArgumentList, SpecTecCall.«$lift_typeArgumentListIR» «typeIR*»⟩) (fun («exec:3» : SpecTec.typeArgumentList) => (let «eval:1» : SpecTec.typeArgumentList := «exec:3»; (let typeArgumentList : SpecTec.typeArgumentList := «eval:1»; (.pure ((((type.«TUPLE `< % `>» typeArgumentList) : type) : type)))))))))) | none => .unmatch))))


noncomputable def «$lift_dataTypeIR:clause:2» (input0 : SpecTec.dataTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let dataTypeIR : SpecTec.dataTypeIR := input0; (.bind (.guard (((«sub:dataTypeIR:arrayTypeIR» dataTypeIR) = true))) (fun (_ : Unit) => (match («$lift_dataTypeIR:case_3:downcast:0» dataTypeIR) with | some «exec:1» => (let «eval:0» : arrayTypeIR := «exec:1»; (match «eval:0» with | .«ARRAY % `[ % `]» «exec:2» «exec:3» => (let typeIR : SpecTec.typeIR := «exec:2»; (let n : _root_.Nat := «exec:3»; (.bind (.call ⟨SpecTec.type, SpecTecCall.«$lift_typeIR» typeIR⟩) (fun («exec:4» : SpecTec.type) => (let «eval:1» : SpecTec.type := «exec:4»; (let type : SpecTec.type := «eval:1»; (.pure ((((SpecTec.type.«% `[ % `]» type ((expression.D (_root_.Int.ofNat n)) : expression)) : SpecTec.type) : SpecTec.type))))))))))) | none => .unmatch))))


noncomputable def «$lift_dataTypeIR:clause:3» (input0 : SpecTec.dataTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let dataTypeIR : SpecTec.dataTypeIR := input0; (.bind (.guard (((«sub:dataTypeIR:headerStackTypeIR» dataTypeIR) = true))) (fun (_ : Unit) => (match («$lift_dataTypeIR:case_4:downcast:0» dataTypeIR) with | some «exec:1» => (let «eval:0» : headerStackTypeIR := «exec:1»; (match «eval:0» with | .«HEADER_STACK % `[ % `]» «exec:2» «exec:3» => (let typeIR : SpecTec.typeIR := «exec:2»; (let n : _root_.Nat := «exec:3»; (.bind (.call ⟨SpecTec.type, SpecTecCall.«$lift_typeIR» typeIR⟩) (fun («exec:4» : SpecTec.type) => (let «eval:1» : SpecTec.type := «exec:4»; (let type : SpecTec.type := «eval:1»; (.pure ((((SpecTec.type.«% `[ % `]» type ((expression.D (_root_.Int.ofNat n)) : expression)) : SpecTec.type) : SpecTec.type))))))))))) | none => .unmatch))))


noncomputable def «$lift_dataTypeIR:clause:4» (input0 : SpecTec.dataTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let dataTypeIR : SpecTec.dataTypeIR := input0; (.bind (.guard (((«sub:dataTypeIR:simpleEnumTypeIR» dataTypeIR) = true))) (fun (_ : Unit) => (match («$lift_dataTypeIR:case_5:downcast:0» dataTypeIR) with | some «exec:1» => (let «eval:0» : simpleEnumTypeIR := «exec:1»; (match «eval:0» with | .«ENUM % `{ % `}» «exec:2» «exec:3» => (let typeId : SpecTec.typeId := «exec:2»; (let «_nameIR*» : (_root_.List nameIR) := «exec:3»; (.bind (.call ⟨SpecTec.typeName, SpecTecCall.«$lift_nameIR_as_typeName» typeId⟩) (fun («exec:4» : SpecTec.typeName) => (let «eval:1» : SpecTec.typeName := «exec:4»; (let typeName : SpecTec.typeName := «eval:1»; (.pure (((«cast:typeIdentifier:type» typeName) : type))))))))))) | none => .unmatch))))


noncomputable def «$lift_dataTypeIR:clause:5» (input0 : SpecTec.dataTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let dataTypeIR : SpecTec.dataTypeIR := input0; (.bind (.guard (((«sub:dataTypeIR:serializableEnumTypeIR» dataTypeIR) = true))) (fun (_ : Unit) => (match («$lift_dataTypeIR:case_6:downcast:0» dataTypeIR) with | some «exec:1» => (let «eval:0» : serializableEnumTypeIR := «exec:1»; (match «eval:0» with | .«ENUM % `< % `> `{ % `}» «exec:2» «exec:3» «exec:4» => (let typeId : SpecTec.typeId := «exec:2»; (let typeIR : SpecTec.typeIR := «exec:3»; (let «_valueFieldIR*» : (_root_.List valueFieldIR) := «exec:4»; (.bind (.call ⟨SpecTec.typeName, SpecTecCall.«$lift_nameIR_as_typeName» typeId⟩) (fun («exec:5» : SpecTec.typeName) => (let «eval:1» : SpecTec.typeName := «exec:5»; (let typeName : SpecTec.typeName := «eval:1»; (.bind (.call ⟨SpecTec.typeArgument, SpecTecCall.«$lift_typeArgumentIR» typeIR⟩) (fun («exec:6» : SpecTec.typeArgument) => (let «eval:2» : SpecTec.typeArgument := «exec:6»; (let typeArgument : SpecTec.typeArgument := «eval:2»; (.pure ((((type.«% `< % `>» («cast:typeIdentifier:prefixedTypeName» typeName) («cast:typeArgument:typeArgumentList» typeArgument)) : type) : type)))))))))))))))) | none => .unmatch))))


noncomputable def «$lift_dataTypeIR_clauses» (input0 : dataTypeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_dataTypeIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_dataTypeIR:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_dataTypeIR:clause:2»  input0), fun (_ : _root_.Unit) => («$lift_dataTypeIR:clause:3»  input0), fun (_ : _root_.Unit) => («$lift_dataTypeIR:clause:4»  input0), fun (_ : _root_.Unit) => («$lift_dataTypeIR:clause:5»  input0)]


noncomputable def «$lift_typeArgumentIR_as_realTypeArgument:clause:0» (input0 : typeArgumentIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:voidTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$lift_typeArgumentIR_as_realTypeArgument:case_1:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.voidTypeIR := «exec:1»; (let voidTypeIR : SpecTec.voidTypeIR := «eval:0»; (.bind (.guard (((SpecTec.voidTypeIR.VOID) : SpecTec.voidTypeIR) = voidTypeIR)) (fun (_ : Unit) => (.pure ((((realTypeArgument.VOID) : realTypeArgument) : realTypeArgument))))))) | none => .unmatch))))


noncomputable def «$lift_typeArgumentIR_as_realTypeArgument:clause:1» (input0 : typeArgumentIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.call ⟨type, SpecTecCall.«$lift_typeIR» typeIR⟩) (fun («exec:1» : type) => (let «eval:0» : type := «exec:1»; (.pure (((«cast:type:realTypeArgument» «eval:0») : realTypeArgument)))))))


noncomputable def «$lift_typeArgumentIR_as_realTypeArgument_clauses» (input0 : typeArgumentIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_typeArgumentIR_as_realTypeArgument:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_typeArgumentIR_as_realTypeArgument:clause:1»  input0)]

end SpecTec
