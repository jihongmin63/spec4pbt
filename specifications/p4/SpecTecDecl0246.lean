import SpecTecDecl0245

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$flatten_objectDeclarationList:clause:1» (input0 : SpecTec.objectDeclarationList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let objectDeclarationList' : SpecTec.objectDeclarationList := input0; (.bind (.guard (((«exec:match:objectDeclarationList:% %» objectDeclarationList') = true))) (fun (_ : Unit) => (match objectDeclarationList' with | .«% %» «exec:1» «exec:2» => (let objectDeclarationList : SpecTec.objectDeclarationList := «exec:1»; (let objectDeclaration : SpecTec.objectDeclaration := «exec:2»; (.bind (.call ⟨(_root_.List SpecTec.objectDeclaration), SpecTecCall.«$flatten_objectDeclarationList» objectDeclarationList⟩) (fun («exec:3» : (_root_.List SpecTec.objectDeclaration)) => (let «eval:0» : (_root_.List SpecTec.objectDeclaration) := «exec:3»; (.pure (((«eval:0» ++ ([objectDeclaration] : (_root_.List SpecTec.objectDeclaration))) : (_root_.List SpecTec.objectDeclaration))))))))) | _ => .unmatch))))


noncomputable def «$flatten_objectDeclarationList_clauses» (input0 : objectDeclarationList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_objectDeclarationList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_objectDeclarationList:clause:1»  input0)]


noncomputable def «$flatten_p4program:clause:0» (input0 : SpecTec.p4program) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p4program : SpecTec.p4program := input0; (.bind (.guard (((«exec:match:p4program:_EMPTY» p4program) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List declaration)) : (_root_.List declaration)))))))


noncomputable def «$flatten_p4program:clause:1» (input0 : SpecTec.p4program) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p4program' : SpecTec.p4program := input0; (.bind (.guard (((«exec:match:p4program:% %» p4program') = true))) (fun (_ : Unit) => (match p4program' with | .«% %» «exec:1» «exec:2» => (let p4program : SpecTec.p4program := «exec:1»; (let declaration : SpecTec.declaration := «exec:2»; (.bind (.call ⟨(_root_.List SpecTec.declaration), SpecTecCall.«$flatten_p4program» p4program⟩) (fun («exec:3» : (_root_.List SpecTec.declaration)) => (let «eval:0» : (_root_.List SpecTec.declaration) := «exec:3»; (.pure (((«eval:0» ++ ([declaration] : (_root_.List SpecTec.declaration))) : (_root_.List SpecTec.declaration))))))))) | _ => .unmatch))))


noncomputable def «$flatten_p4program:clause:2» (input0 : SpecTec.p4program) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p4program' : SpecTec.p4program := input0; (.bind (.guard (((«exec:match:p4program:% ';'» p4program') = true))) (fun (_ : Unit) => (match p4program' with | .«% ';'» «exec:1» => (let p4program : SpecTec.p4program := «exec:1»; (.bind (.call ⟨(_root_.List declaration), SpecTecCall.«$flatten_p4program» p4program⟩) (fun («exec:2» : (_root_.List declaration)) => (let «eval:0» : (_root_.List declaration) := «exec:2»; (.pure ((«eval:0» : (_root_.List declaration)))))))) | _ => .unmatch))))


noncomputable def «$flatten_p4program_clauses» (input0 : p4program) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_p4program:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_p4program:clause:1»  input0), fun (_ : _root_.Unit) => («$flatten_p4program:clause:2»  input0)]


noncomputable def «$flatten_parserBlockElementStatementList:clause:0» (input0 : SpecTec.parserBlockElementStatementList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserBlockElementStatementList : SpecTec.parserBlockElementStatementList := input0; (.bind (.guard (((«exec:match:parserBlockElementStatementList:_EMPTY» parserBlockElementStatementList) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List parserBlockElementStatement)) : (_root_.List parserBlockElementStatement)))))))


noncomputable def «$flatten_parserBlockElementStatementList:clause:1» (input0 : SpecTec.parserBlockElementStatementList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserBlockElementStatementList' : SpecTec.parserBlockElementStatementList := input0; (.bind (.guard (((«exec:match:parserBlockElementStatementList:% %» parserBlockElementStatementList') = true))) (fun (_ : Unit) => (match parserBlockElementStatementList' with | .«% %» «exec:1» «exec:2» => (let parserBlockElementStatementList : SpecTec.parserBlockElementStatementList := «exec:1»; (let parserBlockElementStatement : SpecTec.parserBlockElementStatement := «exec:2»; (.bind (.call ⟨(_root_.List SpecTec.parserBlockElementStatement), SpecTecCall.«$flatten_parserBlockElementStatementList» parserBlockElementStatementList⟩) (fun («exec:3» : (_root_.List SpecTec.parserBlockElementStatement)) => (let «eval:0» : (_root_.List SpecTec.parserBlockElementStatement) := «exec:3»; (.pure (((«eval:0» ++ ([parserBlockElementStatement] : (_root_.List SpecTec.parserBlockElementStatement))) : (_root_.List SpecTec.parserBlockElementStatement))))))))) | _ => .unmatch))))


noncomputable def «$flatten_parserBlockElementStatementList_clauses» (input0 : parserBlockElementStatementList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_parserBlockElementStatementList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_parserBlockElementStatementList:clause:1»  input0)]


noncomputable def «$flatten_parserLocalDeclarationList:clause:0» (input0 : SpecTec.parserLocalDeclarationList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserLocalDeclarationList : SpecTec.parserLocalDeclarationList := input0; (.bind (.guard (((«exec:match:parserLocalDeclarationList:_EMPTY» parserLocalDeclarationList) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List parserLocalDeclaration)) : (_root_.List parserLocalDeclaration)))))))


noncomputable def «$flatten_parserLocalDeclarationList:clause:1» (input0 : SpecTec.parserLocalDeclarationList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserLocalDeclarationList' : SpecTec.parserLocalDeclarationList := input0; (.bind (.guard (((«exec:match:parserLocalDeclarationList:% %» parserLocalDeclarationList') = true))) (fun (_ : Unit) => (match parserLocalDeclarationList' with | .«% %» «exec:1» «exec:2» => (let parserLocalDeclarationList : SpecTec.parserLocalDeclarationList := «exec:1»; (let parserLocalDeclaration : SpecTec.parserLocalDeclaration := «exec:2»; (.bind (.call ⟨(_root_.List SpecTec.parserLocalDeclaration), SpecTecCall.«$flatten_parserLocalDeclarationList» parserLocalDeclarationList⟩) (fun («exec:3» : (_root_.List SpecTec.parserLocalDeclaration)) => (let «eval:0» : (_root_.List SpecTec.parserLocalDeclaration) := «exec:3»; (.pure (((«eval:0» ++ ([parserLocalDeclaration] : (_root_.List SpecTec.parserLocalDeclaration))) : (_root_.List SpecTec.parserLocalDeclaration))))))))) | _ => .unmatch))))


noncomputable def «$flatten_parserLocalDeclarationList_clauses» (input0 : parserLocalDeclarationList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_parserLocalDeclarationList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_parserLocalDeclarationList:clause:1»  input0)]


noncomputable def «$flatten_prefixedNameIR:clause:0» (input0 : SpecTec.prefixedNameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let prefixedNameIR : SpecTec.prefixedNameIR := input0; (.bind (.guard (((«exec:match:prefixedNameIR:_BARE» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | ._BARE «exec:1» => (let nameIR : SpecTec.nameIR := «exec:1»; (.pure ((nameIR : SpecTec.nameIR)))) | _ => .unmatch))))


noncomputable def «$flatten_prefixedNameIR:clause:1» (input0 : SpecTec.prefixedNameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let prefixedNameIR : SpecTec.prefixedNameIR := input0; (.bind (.guard (((«exec:match:prefixedNameIR:'.' %» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | .«'.' %» «exec:1» => (let nameIR : SpecTec.nameIR := «exec:1»; (.pure ((("." ++ nameIR) : SpecTec.nameIR)))) | _ => .unmatch))))


noncomputable def «$flatten_prefixedNameIR_clauses» (input0 : prefixedNameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_prefixedNameIR:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_prefixedNameIR:clause:1»  input0)]


noncomputable def «$lift_prefixedNameIR_as_prefixedNonTypeName:clause:0» (input0 : SpecTec.prefixedNameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let prefixedNameIR : SpecTec.prefixedNameIR := input0; (.bind (.guard (((«exec:match:prefixedNameIR:_BARE» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | ._BARE «exec:1» => (let nameIR : SpecTec.nameIR := «exec:1»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:2» : nonTypeName) => (let «eval:0» : nonTypeName := «exec:2»; (.pure (((«cast:nonTypeName:prefixedNonTypeName» «eval:0») : prefixedNonTypeName))))))) | _ => .unmatch))))


noncomputable def «$lift_prefixedNameIR_as_prefixedNonTypeName:clause:1» (input0 : SpecTec.prefixedNameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let prefixedNameIR : SpecTec.prefixedNameIR := input0; (.bind (.guard (((«exec:match:prefixedNameIR:'.' %» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | .«'.' %» «exec:1» => (let nameIR : SpecTec.nameIR := «exec:1»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:2» : nonTypeName) => (let «eval:0» : nonTypeName := «exec:2»; (.pure ((((prefixedNonTypeName.«_ID '.' %» «eval:0») : prefixedNonTypeName) : prefixedNonTypeName))))))) | _ => .unmatch))))


noncomputable def «$lift_prefixedNameIR_as_prefixedNonTypeName_clauses» (input0 : prefixedNameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_prefixedNameIR_as_prefixedNonTypeName:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_prefixedNameIR_as_prefixedNonTypeName:clause:1»  input0)]


noncomputable def «$lift_prefixedNameIR_as_prefixedTypeName:clause:0» (input0 : SpecTec.prefixedNameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let prefixedNameIR : SpecTec.prefixedNameIR := input0; (.bind (.guard (((«exec:match:prefixedNameIR:_BARE» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | ._BARE «exec:1» => (let nameIR : SpecTec.nameIR := «exec:1»; (.bind (.call ⟨typeName, SpecTecCall.«$lift_nameIR_as_typeName» nameIR⟩) (fun («exec:2» : typeName) => (let «eval:0» : typeName := «exec:2»; (.pure (((«cast:typeIdentifier:prefixedTypeName» «eval:0») : prefixedTypeName))))))) | _ => .unmatch))))


noncomputable def «$lift_prefixedNameIR_as_prefixedTypeName:clause:1» (input0 : SpecTec.prefixedNameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let prefixedNameIR : SpecTec.prefixedNameIR := input0; (.bind (.guard (((«exec:match:prefixedNameIR:'.' %» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | .«'.' %» «exec:1» => (let nameIR : SpecTec.nameIR := «exec:1»; (.bind (.call ⟨typeName, SpecTecCall.«$lift_nameIR_as_typeName» nameIR⟩) (fun («exec:2» : typeName) => (let «eval:0» : typeName := «exec:2»; (.pure ((((prefixedTypeName.«_TID '.' %» «eval:0») : prefixedTypeName) : prefixedTypeName))))))) | _ => .unmatch))))


noncomputable def «$lift_prefixedNameIR_as_prefixedTypeName_clauses» (input0 : prefixedNameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_prefixedNameIR_as_prefixedTypeName:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_prefixedNameIR_as_prefixedTypeName:clause:1»  input0)]


noncomputable def «$lift_referenceExpressionIR:clause:0» (input0 : referenceExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let prefixedNameIR : SpecTec.prefixedNameIR := input0; (.bind (.guard (((«exec:match:prefixedNameIR:_BARE» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | ._BARE «exec:1» => (let nameIR : SpecTec.nameIR := «exec:1»; (.bind (.guard ("this" = nameIR)) (fun (_ : Unit) => (.pure ((((referenceExpression.THIS) : referenceExpression) : referenceExpression)))))) | _ => .unmatch))))


noncomputable def «$lift_referenceExpressionIR:clause:1» (input0 : referenceExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let prefixedNameIR : SpecTec.prefixedNameIR := input0; (.bind (.guard (((«exec:match:prefixedNameIR:_BARE» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | ._BARE «exec:1» => (let nameIR : SpecTec.nameIR := «exec:1»; (.bind (.guard ((nameIR ≠ "this"))) (fun (_ : Unit) => (.bind (.call ⟨SpecTec.nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:2» : SpecTec.nonTypeName) => (let «eval:0» : SpecTec.nonTypeName := «exec:2»; (let nonTypeName : SpecTec.nonTypeName := «eval:0»; (.pure (((«cast:nonTypeName:referenceExpression» nonTypeName) : referenceExpression)))))))))) | _ => .unmatch))))


noncomputable def «$lift_referenceExpressionIR:clause:2» (input0 : referenceExpressionIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let prefixedNameIR : SpecTec.prefixedNameIR := input0; (.bind (.guard (((«exec:match:prefixedNameIR:'.' %» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | .«'.' %» «exec:1» => (let nameIR : SpecTec.nameIR := «exec:1»; (.bind (.call ⟨SpecTec.nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:2» : SpecTec.nonTypeName) => (let «eval:0» : SpecTec.nonTypeName := «exec:2»; (let nonTypeName : SpecTec.nonTypeName := «eval:0»; (.pure ((((referenceExpression.«_ID '.' %» nonTypeName) : referenceExpression) : referenceExpression)))))))) | _ => .unmatch))))


noncomputable def «$lift_referenceExpressionIR_clauses» (input0 : referenceExpressionIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_referenceExpressionIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_referenceExpressionIR:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_referenceExpressionIR:clause:2»  input0)]


noncomputable def «$find_var_t:clause:0» (input0 : SpecTec.prefixedNameIR) (input1 : cursor) (input2 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let prefixedNameIR : SpecTec.prefixedNameIR := input0; (let p : cursor := input1; (let TC : typingContext := input2; (.bind (.guard (((«exec:match:prefixedNameIR:'.' %» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | .«'.' %» «exec:1» => (let id : SpecTec.id := «exec:1»; (let typeFrame : SpecTec.typeFrame := (globalTypingLayer.FRAME (typingContext.GLOBAL TC)); (.bind (.call ⟨(_root_.Option varTypeIR), SpecTecCall.«$find_map» SpecTec.id varTypeIR typeFrame id⟩) (fun («exec:2» : (_root_.Option varTypeIR)) => (let «eval:0» : (_root_.Option varTypeIR) := «exec:2»; (.pure ((«eval:0» : (_root_.Option varTypeIR))))))))) | _ => .unmatch))))))


noncomputable def «$find_var_t:clause:1» (input0 : SpecTec.prefixedNameIR) (input1 : cursor) (input2 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let prefixedNameIR : SpecTec.prefixedNameIR := input0; (let p : cursor := input1; (let TC : typingContext := input2; (.bind (.guard (((«exec:match:prefixedNameIR:_BARE» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | ._BARE «exec:1» => (let id : SpecTec.id := «exec:1»; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (let typeFrame : SpecTec.typeFrame := (globalTypingLayer.FRAME (typingContext.GLOBAL TC)); (.bind (.call ⟨(_root_.Option varTypeIR), SpecTecCall.«$find_map» SpecTec.id varTypeIR typeFrame id⟩) (fun («exec:2» : (_root_.Option varTypeIR)) => (let «eval:0» : (_root_.Option varTypeIR) := «exec:2»; (.pure ((«eval:0» : (_root_.Option varTypeIR))))))))))) | _ => .unmatch))))))


noncomputable def «$find_var_t:clause:2» (input0 : SpecTec.prefixedNameIR) (input1 : cursor) (input2 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let prefixedNameIR : SpecTec.prefixedNameIR := input0; (let p : cursor := input1; (let TC : typingContext := input2; (.bind (.guard (((«exec:match:prefixedNameIR:_BARE» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | ._BARE «exec:1» => (let id : SpecTec.id := «exec:1»; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (let typeFrame : SpecTec.typeFrame := (blockTypingLayer.FRAME (typingContext.BLOCK TC)); (.bind (.call ⟨(_root_.Option SpecTec.varTypeIR), SpecTecCall.«$find_map» SpecTec.id SpecTec.varTypeIR typeFrame id⟩) (fun («exec:2» : (_root_.Option SpecTec.varTypeIR)) => (let «eval:0» : (_root_.Option SpecTec.varTypeIR) := «exec:2»; (let varTypeIR'? : (_root_.Option SpecTec.varTypeIR) := «eval:0»; (.bind (.guard (((_root_.Option.isSome varTypeIR'?) = true))) (fun (_ : Unit) => (match varTypeIR'? with | some «exec:3» => (let varTypeIR : SpecTec.varTypeIR := «exec:3»; (.pure (((_root_.Option.some varTypeIR) : (_root_.Option SpecTec.varTypeIR))))) | none => .unmatch))))))))))) | _ => .unmatch))))))


noncomputable def «$find_var_t:clause:3» (input0 : SpecTec.prefixedNameIR) (input1 : cursor) (input2 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let prefixedNameIR : SpecTec.prefixedNameIR := input0; (let p : cursor := input1; (let TC : typingContext := input2; (.bind (.guard (((«exec:match:prefixedNameIR:_BARE» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | ._BARE «exec:1» => (let id : SpecTec.id := «exec:1»; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (let typeFrame : SpecTec.typeFrame := (blockTypingLayer.FRAME (typingContext.BLOCK TC)); (.bind (.call ⟨(_root_.Option varTypeIR), SpecTecCall.«$find_map» SpecTec.id varTypeIR typeFrame id⟩) (fun («exec:2» : (_root_.Option varTypeIR)) => (let «eval:0» : (_root_.Option varTypeIR) := «exec:2»; (match «eval:0» with | none => (.bind (.call ⟨(_root_.Option varTypeIR), SpecTecCall.«$find_var_t» ((SpecTec.prefixedNameIR._BARE id) : SpecTec.prefixedNameIR) ((cursor.GLOBAL) : cursor) TC⟩) (fun («exec:3» : (_root_.Option varTypeIR)) => (let «eval:1» : (_root_.Option varTypeIR) := «exec:3»; (.pure ((«eval:1» : (_root_.Option varTypeIR))))))) | some _ => .unmatch)))))))) | _ => .unmatch))))))


noncomputable def «$find_var_t:clause:4» (input0 : SpecTec.prefixedNameIR) (input1 : cursor) (input2 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let prefixedNameIR : SpecTec.prefixedNameIR := input0; (let p : cursor := input1; (let TC : typingContext := input2; (.bind (.guard (((«exec:match:prefixedNameIR:_BARE» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | ._BARE «exec:1» => (let id : SpecTec.id := «exec:1»; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (let «typeFrame*» : (_root_.List typeFrame) := (localTypingLayer.FRAMES (typingContext.LOCAL TC)); (.bind (.call ⟨(_root_.Option SpecTec.varTypeIR), SpecTecCall.«$find_maps» SpecTec.id SpecTec.varTypeIR «typeFrame*» id⟩) (fun («exec:2» : (_root_.Option SpecTec.varTypeIR)) => (let «eval:0» : (_root_.Option SpecTec.varTypeIR) := «exec:2»; (let varTypeIR'? : (_root_.Option SpecTec.varTypeIR) := «eval:0»; (.bind (.guard (((_root_.Option.isSome varTypeIR'?) = true))) (fun (_ : Unit) => (match varTypeIR'? with | some «exec:3» => (let varTypeIR : SpecTec.varTypeIR := «exec:3»; (.pure (((_root_.Option.some varTypeIR) : (_root_.Option SpecTec.varTypeIR))))) | none => .unmatch))))))))))) | _ => .unmatch))))))


noncomputable def «$find_var_t:clause:5» (input0 : SpecTec.prefixedNameIR) (input1 : cursor) (input2 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let prefixedNameIR : SpecTec.prefixedNameIR := input0; (let p : cursor := input1; (let TC : typingContext := input2; (.bind (.guard (((«exec:match:prefixedNameIR:_BARE» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | ._BARE «exec:1» => (let id : SpecTec.id := «exec:1»; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (let «typeFrame*» : (_root_.List typeFrame) := (localTypingLayer.FRAMES (typingContext.LOCAL TC)); (.bind (.call ⟨(_root_.Option varTypeIR), SpecTecCall.«$find_maps» SpecTec.id varTypeIR «typeFrame*» id⟩) (fun («exec:2» : (_root_.Option varTypeIR)) => (let «eval:0» : (_root_.Option varTypeIR) := «exec:2»; (match «eval:0» with | none => (.bind (.call ⟨(_root_.Option varTypeIR), SpecTecCall.«$find_var_t» ((SpecTec.prefixedNameIR._BARE id) : SpecTec.prefixedNameIR) ((cursor.BLOCK) : cursor) TC⟩) (fun («exec:3» : (_root_.Option varTypeIR)) => (let «eval:1» : (_root_.Option varTypeIR) := «exec:3»; (.pure ((«eval:1» : (_root_.Option varTypeIR))))))) | some _ => .unmatch)))))))) | _ => .unmatch))))))


noncomputable def «$find_var_t_clauses» (input0 : prefixedNameIR) (input1 : cursor) (input2 : typingContext) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_var_t:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$find_var_t:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$find_var_t:clause:2»  input0 input1 input2), fun (_ : _root_.Unit) => («$find_var_t:clause:3»  input0 input1 input2), fun (_ : _root_.Unit) => («$find_var_t:clause:4»  input0 input1 input2), fun (_ : _root_.Unit) => («$find_var_t:clause:5»  input0 input1 input2)]

end SpecTec
