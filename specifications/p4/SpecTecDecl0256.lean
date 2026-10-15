import SpecTecDecl0255

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$align_parameterListIR_clauses» (input0 : (_root_.List parameterIR)) (input1 : (_root_.List argumentIR)) (input2 : (_root_.List nameIR)) (input3 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_parameterListIR:clause:0»  input0 input1 input2 input3)]


noncomputable def «$callTargetKey':clause:0» (input0 : SpecTec.argumentIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let argumentIR : SpecTec.argumentIR := input0; (.bind (.guard (((«sub:argumentIR:typedExpressionIR» argumentIR) = true))) (fun (_ : Unit) => (match («$callTargetKey':case_1:downcast:0» argumentIR) with | some «exec:1» => (let «eval:0» : SpecTec.typedExpressionIR := «exec:1»; (let typedExpressionIR : SpecTec.typedExpressionIR := «eval:0»; (.pure ((((_root_.Option.none) : (_root_.Option id)) : (_root_.Option id)))))) | none => .unmatch))))


noncomputable def «$callTargetKey':clause:1» (input0 : SpecTec.argumentIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let argumentIR : SpecTec.argumentIR := input0; (.bind (.guard (((«exec:match:argumentIR:% '=' %» argumentIR) = true))) (fun (_ : Unit) => (match argumentIR with | .«% '=' %» «exec:1» «exec:2» => (let id_arg : id := «exec:1»; (let _typedExpressionIR : typedExpressionIR := «exec:2»; (.pure (((_root_.Option.some id_arg) : (_root_.Option id)))))) | _ => .unmatch))))


noncomputable def «$callTargetKey':clause:2» (input0 : SpecTec.argumentIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let argumentIR : SpecTec.argumentIR := input0; (.bind (.guard (((«exec:match:argumentIR:% '=' '_'» argumentIR) = true))) (fun (_ : Unit) => (match argumentIR with | .«% '=' '_'» «exec:1» => (let id_arg : id := «exec:1»; (.pure (((_root_.Option.some id_arg) : (_root_.Option id))))) | _ => .unmatch))))


noncomputable def «$callTargetKey':clause:3» (input0 : SpecTec.argumentIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let argumentIR : SpecTec.argumentIR := input0; (.bind (.guard (((«exec:match:argumentIR:'_'» argumentIR) = true))) (fun (_ : Unit) => (.pure ((((_root_.Option.none) : (_root_.Option id)) : (_root_.Option id)))))))


noncomputable def «$callTargetKey'_clauses» (input0 : argumentIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$callTargetKey':clause:0»  input0), fun (_ : _root_.Unit) => («$callTargetKey':clause:1»  input0), fun (_ : _root_.Unit) => («$callTargetKey':clause:2»  input0), fun (_ : _root_.Unit) => («$callTargetKey':clause:3»  input0)]


noncomputable def «$callTargetKey:case_1:iter:0:clause:0» (input0 : (_root_.List argumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.Option id))) : (_root_.List (_root_.Option id))))) | _ :: _ => .unmatch)


noncomputable def «$callTargetKey:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.argumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let argumentIR : SpecTec.argumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.argumentIR) := «exec:1»; (.bind (.call ⟨(_root_.Option id), SpecTecCall.«$callTargetKey'» argumentIR⟩) (fun («exec:3» : (_root_.Option id)) => (let «eval:1» : (_root_.Option id) := «exec:3»; (let id_arg? : (_root_.Option id) := «eval:1»; (.bind (.call ⟨(_root_.List (_root_.Option id)), SpecTecCall.«$callTargetKey:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.Option id))) => (let «tail:1» : (_root_.List (_root_.Option id)) := «exec:4»; (.pure (((id_arg? :: «tail:1») : (_root_.List (_root_.Option id)))))))))))))) | [] => .unmatch)


noncomputable def «$callTargetKey:case_1:iter:0_clauses» (input0 : (_root_.List argumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$callTargetKey:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$callTargetKey:case_1:iter:0:clause:1»  input0)]


noncomputable def «$callTargetKey:clause:0» (input0 : nameIR) (input1 : argumentListIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR_f : nameIR := input0; (let «argumentIR*» : (_root_.List argumentIR) := input1; (.bind (.call ⟨(_root_.List (_root_.Option id)), SpecTecCall.«$callTargetKey:case_1:iter:0» «argumentIR*»⟩) (fun («exec:1» : (_root_.List (_root_.Option id))) => (let «id_arg?*» : (_root_.List (_root_.Option id)) := «exec:1»; (.pure ((((callTargetKey.«% `( % `)» nameIR_f «id_arg?*») : callTargetKey) : callTargetKey))))))))


noncomputable def «$callTargetKey_clauses» (input0 : nameIR) (input1 : argumentListIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$callTargetKey:clause:0»  input0 input1)]


noncomputable def «$find_constructorDef_overloaded_t:clause:0» (input0 : typingContext) (input1 : SpecTec.prefixedNameIR) (input2 : (_root_.List argumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC : typingContext := input0; (let prefixedNameIR : SpecTec.prefixedNameIR := input1; (let «argumentIR*» : (_root_.List argumentIR) := input2; (.bind (.guard (((«exec:match:prefixedNameIR:'.' %» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | .«'.' %» «exec:1» => (let nameIR : SpecTec.nameIR := «exec:1»; (.bind (.call ⟨SpecTec.callTargetKey, SpecTecCall.«$callTargetKey» nameIR «argumentIR*»⟩) (fun («exec:2» : SpecTec.callTargetKey) => (let «eval:0» : SpecTec.callTargetKey := «exec:2»; (let callTargetKey : SpecTec.callTargetKey := «eval:0»; (.bind (.call ⟨(_root_.Option (callResolution constructorTypeDefIR)), SpecTecCall.«$find_overloaded» constructorTypeDefIR (globalTypingLayer.CONSTRUCTOR (typingContext.GLOBAL TC)) callTargetKey SpecTecCall.«$parameterListIR_of_constructorTypeDefIR»⟩) (fun («exec:3» : (_root_.Option (callResolution constructorTypeDefIR))) => (let «eval:1» : (_root_.Option (callResolution constructorTypeDefIR)) := «exec:3»; (.pure ((«eval:1» : (_root_.Option (callResolution constructorTypeDefIR))))))))))))) | _ => .unmatch))))))


noncomputable def «$find_constructorDef_overloaded_t:clause:1» (input0 : typingContext) (input1 : SpecTec.prefixedNameIR) (input2 : (_root_.List argumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC : typingContext := input0; (let prefixedNameIR : SpecTec.prefixedNameIR := input1; (let «argumentIR*» : (_root_.List argumentIR) := input2; (.bind (.guard (((«exec:match:prefixedNameIR:_BARE» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | ._BARE «exec:1» => (let nameIR : SpecTec.nameIR := «exec:1»; (.bind (.call ⟨SpecTec.callTargetKey, SpecTecCall.«$callTargetKey» nameIR «argumentIR*»⟩) (fun («exec:2» : SpecTec.callTargetKey) => (let «eval:0» : SpecTec.callTargetKey := «exec:2»; (let callTargetKey : SpecTec.callTargetKey := «eval:0»; (.bind (.call ⟨(_root_.Option (callResolution constructorTypeDefIR)), SpecTecCall.«$find_overloaded» constructorTypeDefIR (globalTypingLayer.CONSTRUCTOR (typingContext.GLOBAL TC)) callTargetKey SpecTecCall.«$parameterListIR_of_constructorTypeDefIR»⟩) (fun («exec:3» : (_root_.Option (callResolution constructorTypeDefIR))) => (let «eval:1» : (_root_.Option (callResolution constructorTypeDefIR)) := «exec:3»; (.pure ((«eval:1» : (_root_.Option (callResolution constructorTypeDefIR))))))))))))) | _ => .unmatch))))))


noncomputable def «$find_constructorDef_overloaded_t_clauses» (input0 : typingContext) (input1 : prefixedNameIR) (input2 : (_root_.List argumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_constructorDef_overloaded_t:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$find_constructorDef_overloaded_t:clause:1»  input0 input1 input2)]


noncomputable def «$flatten_argumentList:clause:0» (input0 : SpecTec.argumentList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let argumentList : SpecTec.argumentList := input0; (.bind (.guard (((«exec:match:argumentList:_EMPTY» argumentList) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List argument)) : (_root_.List argument)))))))


noncomputable def «$flatten_argumentList:clause:1» (input0 : SpecTec.argumentList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let argumentList : SpecTec.argumentList := input0; (.bind (.guard (((«sub:argumentList:argument» argumentList) = true))) (fun (_ : Unit) => (match («$flatten_argumentList:case_2:downcast:0» argumentList) with | some «exec:1» => (let «eval:0» : SpecTec.argument := «exec:1»; (let argument : SpecTec.argument := «eval:0»; (.pure ((([argument] : (_root_.List SpecTec.argument)) : (_root_.List SpecTec.argument)))))) | none => .unmatch))))


noncomputable def «$flatten_argumentList:clause:2» (input0 : SpecTec.argumentList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let argumentList : SpecTec.argumentList := input0; (.bind (.guard (((«sub:argumentList:argumentListNonEmpty» argumentList) = true))) (fun (_ : Unit) => (match («$flatten_argumentList:case_3:downcast:0» argumentList) with | some «exec:1» => (let «eval:0» : SpecTec.argumentListNonEmpty := «exec:1»; (let argumentListNonEmpty' : SpecTec.argumentListNonEmpty := «eval:0»; (.bind (.guard (((«exec:match:argumentListNonEmpty:% ',' %» argumentListNonEmpty') = true))) (fun (_ : Unit) => (match argumentListNonEmpty' with | .«% ',' %» «exec:2» «exec:3» => (let argumentListNonEmpty : SpecTec.argumentListNonEmpty := «exec:2»; (let argument : SpecTec.argument := «exec:3»; (.bind (.call ⟨(_root_.List SpecTec.argument), SpecTecCall.«$flatten_argumentList» («cast:argumentListNonEmpty:argumentList» argumentListNonEmpty)⟩) (fun («exec:4» : (_root_.List SpecTec.argument)) => (let «eval:1» : (_root_.List SpecTec.argument) := «exec:4»; (.pure (((«eval:1» ++ ([argument] : (_root_.List SpecTec.argument))) : (_root_.List SpecTec.argument))))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$flatten_argumentList_clauses» (input0 : argumentList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_argumentList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_argumentList:clause:1»  input0), fun (_ : _root_.Unit) => («$flatten_argumentList:clause:2»  input0)]


noncomputable def «$lift_baseTypeIR:clause:0» (input0 : SpecTec.baseTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let baseTypeIR : SpecTec.baseTypeIR := input0; (.bind (.guard (((«sub:baseTypeIR:boolTypeIR» baseTypeIR) = true))) (fun (_ : Unit) => (match («$lift_baseTypeIR:case_1:downcast:0» baseTypeIR) with | some «exec:1» => (let «eval:0» : SpecTec.boolTypeIR := «exec:1»; (let boolTypeIR : SpecTec.boolTypeIR := «eval:0»; (.bind (.guard (((SpecTec.boolTypeIR.BOOL) : SpecTec.boolTypeIR) = boolTypeIR)) (fun (_ : Unit) => (.pure ((((baseType.BOOL) : baseType) : baseType))))))) | none => .unmatch))))


noncomputable def «$lift_baseTypeIR:clause:1» (input0 : SpecTec.baseTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let baseTypeIR : SpecTec.baseTypeIR := input0; (.bind (.guard (((«sub:baseTypeIR:errorTypeIR» baseTypeIR) = true))) (fun (_ : Unit) => (match («$lift_baseTypeIR:case_2:downcast:0» baseTypeIR) with | some «exec:1» => (let «eval:0» : SpecTec.errorTypeIR := «exec:1»; (let errorTypeIR : SpecTec.errorTypeIR := «eval:0»; (.bind (.guard (((SpecTec.errorTypeIR.ERROR) : SpecTec.errorTypeIR) = errorTypeIR)) (fun (_ : Unit) => (.pure ((((baseType.ERROR) : baseType) : baseType))))))) | none => .unmatch))))


noncomputable def «$lift_baseTypeIR:clause:2» (input0 : SpecTec.baseTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let baseTypeIR : SpecTec.baseTypeIR := input0; (.bind (.guard (((«sub:baseTypeIR:errorTypeIR» baseTypeIR) = true))) (fun (_ : Unit) => (match («$lift_baseTypeIR:case_3:downcast:0» baseTypeIR) with | some «exec:1» => (let «eval:0» : SpecTec.errorTypeIR := «exec:1»; (let errorTypeIR : SpecTec.errorTypeIR := «eval:0»; (.bind (.guard (((SpecTec.errorTypeIR.ERROR) : SpecTec.errorTypeIR) = errorTypeIR)) (fun (_ : Unit) => (.pure ((((baseType.ERROR) : baseType) : baseType))))))) | none => .unmatch))))


noncomputable def «$lift_baseTypeIR:clause:3» (input0 : SpecTec.baseTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let baseTypeIR : SpecTec.baseTypeIR := input0; (.bind (.guard (((«sub:baseTypeIR:matchKindTypeIR» baseTypeIR) = true))) (fun (_ : Unit) => (match («$lift_baseTypeIR:case_4:downcast:0» baseTypeIR) with | some «exec:1» => (let «eval:0» : SpecTec.matchKindTypeIR := «exec:1»; (let matchKindTypeIR : SpecTec.matchKindTypeIR := «eval:0»; (.bind (.guard (((SpecTec.matchKindTypeIR.MATCH_KIND) : SpecTec.matchKindTypeIR) = matchKindTypeIR)) (fun (_ : Unit) => (.pure ((((baseType.MATCH_KIND) : baseType) : baseType))))))) | none => .unmatch))))


noncomputable def «$lift_baseTypeIR:clause:4» (input0 : SpecTec.baseTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let baseTypeIR : SpecTec.baseTypeIR := input0; (.bind (.guard (((«sub:baseTypeIR:stringTypeIR» baseTypeIR) = true))) (fun (_ : Unit) => (match («$lift_baseTypeIR:case_5:downcast:0» baseTypeIR) with | some «exec:1» => (let «eval:0» : SpecTec.stringTypeIR := «exec:1»; (let stringTypeIR : SpecTec.stringTypeIR := «eval:0»; (.bind (.guard (((SpecTec.stringTypeIR.STRING) : SpecTec.stringTypeIR) = stringTypeIR)) (fun (_ : Unit) => (.pure ((((baseType.STRING) : baseType) : baseType))))))) | none => .unmatch))))


noncomputable def «$lift_baseTypeIR:clause:5» (input0 : SpecTec.baseTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let baseTypeIR : SpecTec.baseTypeIR := input0; (.bind (.guard (((«sub:baseTypeIR:intTypeIR» baseTypeIR) = true))) (fun (_ : Unit) => (match («$lift_baseTypeIR:case_6:downcast:0» baseTypeIR) with | some «exec:1» => (let «eval:0» : SpecTec.intTypeIR := «exec:1»; (let intTypeIR : SpecTec.intTypeIR := «eval:0»; (.bind (.guard (((SpecTec.intTypeIR.INT) : SpecTec.intTypeIR) = intTypeIR)) (fun (_ : Unit) => (.pure ((((baseType.INT) : baseType) : baseType))))))) | none => .unmatch))))


noncomputable def «$lift_baseTypeIR:clause:6» (input0 : SpecTec.baseTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let baseTypeIR : SpecTec.baseTypeIR := input0; (.bind (.guard (((«sub:baseTypeIR:fixedIntTypeIR» baseTypeIR) = true))) (fun (_ : Unit) => (match («$lift_baseTypeIR:case_7:downcast:0» baseTypeIR) with | some «exec:1» => (let «eval:0» : fixedIntTypeIR := «exec:1»; (match «eval:0» with | .«INT `< % `>» «exec:2» => (let w : _root_.Nat := «exec:2»; (.pure ((((baseType.«INT `< % `>» (_root_.Int.ofNat w)) : baseType) : baseType)))))) | none => .unmatch))))


noncomputable def «$lift_baseTypeIR:clause:7» (input0 : SpecTec.baseTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let baseTypeIR : SpecTec.baseTypeIR := input0; (.bind (.guard (((«sub:baseTypeIR:fixedBitTypeIR» baseTypeIR) = true))) (fun (_ : Unit) => (match («$lift_baseTypeIR:case_8:downcast:0» baseTypeIR) with | some «exec:1» => (let «eval:0» : fixedBitTypeIR := «exec:1»; (match «eval:0» with | .«BIT `< % `>» «exec:2» => (let w : _root_.Nat := «exec:2»; (.pure ((((baseType.«BIT `< % `>» (_root_.Int.ofNat w)) : baseType) : baseType)))))) | none => .unmatch))))


noncomputable def «$lift_baseTypeIR:clause:8» (input0 : SpecTec.baseTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let baseTypeIR : SpecTec.baseTypeIR := input0; (.bind (.guard (((«sub:baseTypeIR:varBitTypeIR» baseTypeIR) = true))) (fun (_ : Unit) => (match («$lift_baseTypeIR:case_9:downcast:0» baseTypeIR) with | some «exec:1» => (let «eval:0» : varBitTypeIR := «exec:1»; (match «eval:0» with | .«VARBIT `< % `>» «exec:2» => (let w : _root_.Nat := «exec:2»; (.pure ((((baseType.«VARBIT `< % `>» (_root_.Int.ofNat w)) : baseType) : baseType)))))) | none => .unmatch))))


noncomputable def «$lift_baseTypeIR_clauses» (input0 : baseTypeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_baseTypeIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_baseTypeIR:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_baseTypeIR:clause:2»  input0), fun (_ : _root_.Unit) => («$lift_baseTypeIR:clause:3»  input0), fun (_ : _root_.Unit) => («$lift_baseTypeIR:clause:4»  input0), fun (_ : _root_.Unit) => («$lift_baseTypeIR:clause:5»  input0), fun (_ : _root_.Unit) => («$lift_baseTypeIR:clause:6»  input0), fun (_ : _root_.Unit) => («$lift_baseTypeIR:clause:7»  input0), fun (_ : _root_.Unit) => («$lift_baseTypeIR:clause:8»  input0)]


noncomputable def «$signature_of_builtinMethodTypeIR:clause:0» (input0 : SpecTec.builtinMethodTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let builtinMethodTypeIR : SpecTec.builtinMethodTypeIR := input0; (.bind (.guard (((«sub:builtinMethodTypeIR:builtinIsValidMethodTypeIR» builtinMethodTypeIR) = true))) (fun (_ : Unit) => (match («$signature_of_builtinMethodTypeIR:case_1:downcast:0» builtinMethodTypeIR) with | some «exec:1» => (let «eval:0» : SpecTec.builtinIsValidMethodTypeIR := «exec:1»; (let builtinIsValidMethodTypeIR : SpecTec.builtinIsValidMethodTypeIR := «eval:0»; (.bind (.guard (((SpecTec.builtinIsValidMethodTypeIR.BUILTIN_IS_VALID) : SpecTec.builtinIsValidMethodTypeIR) = builtinIsValidMethodTypeIR)) (fun (_ : Unit) => (.pure (((([] : (_root_.List parameterIR)), ((typeIR.BOOL) : typeIR)) : ((_root_.List parameterIR) × typeIR)))))))) | none => .unmatch))))


noncomputable def «$signature_of_builtinMethodTypeIR:clause:1» (input0 : SpecTec.builtinMethodTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let builtinMethodTypeIR : SpecTec.builtinMethodTypeIR := input0; (.bind (.guard (((«sub:builtinMethodTypeIR:builtinSetValidMethodTypeIR» builtinMethodTypeIR) = true))) (fun (_ : Unit) => (match («$signature_of_builtinMethodTypeIR:case_2:downcast:0» builtinMethodTypeIR) with | some «exec:1» => (let «eval:0» : SpecTec.builtinSetValidMethodTypeIR := «exec:1»; (let builtinSetValidMethodTypeIR : SpecTec.builtinSetValidMethodTypeIR := «eval:0»; (.bind (.guard (((SpecTec.builtinSetValidMethodTypeIR.BUILTIN_SET_VALID) : SpecTec.builtinSetValidMethodTypeIR) = builtinSetValidMethodTypeIR)) (fun (_ : Unit) => (.pure (((([] : (_root_.List parameterIR)), ((typeIR.VOID) : typeIR)) : ((_root_.List parameterIR) × typeIR)))))))) | none => .unmatch))))


noncomputable def «$signature_of_builtinMethodTypeIR:clause:2» (input0 : SpecTec.builtinMethodTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let builtinMethodTypeIR : SpecTec.builtinMethodTypeIR := input0; (.bind (.guard (((«sub:builtinMethodTypeIR:builtinSetInvalidMethodTypeIR» builtinMethodTypeIR) = true))) (fun (_ : Unit) => (match («$signature_of_builtinMethodTypeIR:case_3:downcast:0» builtinMethodTypeIR) with | some «exec:1» => (let «eval:0» : SpecTec.builtinSetInvalidMethodTypeIR := «exec:1»; (let builtinSetInvalidMethodTypeIR : SpecTec.builtinSetInvalidMethodTypeIR := «eval:0»; (.bind (.guard (((SpecTec.builtinSetInvalidMethodTypeIR.BUILTIN_SET_INVALID) : SpecTec.builtinSetInvalidMethodTypeIR) = builtinSetInvalidMethodTypeIR)) (fun (_ : Unit) => (.pure (((([] : (_root_.List parameterIR)), ((typeIR.VOID) : typeIR)) : ((_root_.List parameterIR) × typeIR)))))))) | none => .unmatch))))


noncomputable def «$signature_of_builtinMethodTypeIR:clause:3» (input0 : SpecTec.builtinMethodTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let builtinMethodTypeIR : SpecTec.builtinMethodTypeIR := input0; (.bind (.guard (((«sub:builtinMethodTypeIR:builtinPushFrontMethodTypeIR» builtinMethodTypeIR) = true))) (fun (_ : Unit) => (match («$signature_of_builtinMethodTypeIR:case_4:downcast:0» builtinMethodTypeIR) with | some «exec:1» => (let «eval:0» : SpecTec.builtinPushFrontMethodTypeIR := «exec:1»; (let builtinPushFrontMethodTypeIR : SpecTec.builtinPushFrontMethodTypeIR := «eval:0»; (.bind (.guard (((SpecTec.builtinPushFrontMethodTypeIR.BUILTIN_PUSH_FRONT) : SpecTec.builtinPushFrontMethodTypeIR) = builtinPushFrontMethodTypeIR)) (fun (_ : Unit) => (.pure (((([((parameterIR.«% % % % %» ((annotationList._EMPTY) : annotationList) ((direction._EMPTY) : direction) ((typeIR.INT) : typeIR) "count" ((_root_.Option.none) : (_root_.Option parameterInitializerIR))) : parameterIR)] : (_root_.List parameterIR)), ((typeIR.VOID) : typeIR)) : ((_root_.List parameterIR) × typeIR)))))))) | none => .unmatch))))

end SpecTec
