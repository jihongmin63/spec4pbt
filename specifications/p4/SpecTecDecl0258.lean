import SpecTecDecl0257

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$typeParameterListIR_of_callableTypeDefIR:clause:2» (input0 : SpecTec.callableTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTypeDefIR : SpecTec.callableTypeDefIR := input0; (.bind (.guard (((«sub:callableTypeDefIR:externFunctionTypeDefIR» callableTypeDefIR) = true))) (fun (_ : Unit) => (match («$typeParameterListIR_of_callableTypeDefIR:case_3:downcast:0» callableTypeDefIR) with | some «exec:1» => (let «eval:0» : externFunctionTypeDefIR := «exec:1»; (match «eval:0» with | .«EXTERN_FUNCTION % `< % ',' % `> `( % `) ':' %» «exec:2» «exec:3» «exec:4» «exec:5» «exec:6» => (let _nameIR : nameIR := «exec:2»; (let «typeParameterIR_expl*» : (_root_.List typeParameterIR) := «exec:3»; (let «typeParameterIR_impl*» : (_root_.List typeParameterIR) := «exec:4»; (let «_parameterIR*» : (_root_.List parameterIR) := «exec:5»; (let _typeIR : typeIR := «exec:6»; (.pure (((«typeParameterIR_expl*», «typeParameterIR_impl*») : ((_root_.List typeParameterIR) × (_root_.List typeParameterIR)))))))))))) | none => .unmatch))))


noncomputable def «$typeParameterListIR_of_callableTypeDefIR:clause:3» (input0 : SpecTec.callableTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTypeDefIR : SpecTec.callableTypeDefIR := input0; (.bind (.guard (((«sub:callableTypeDefIR:externMethodTypeDefIR» callableTypeDefIR) = true))) (fun (_ : Unit) => (match («$typeParameterListIR_of_callableTypeDefIR:case_4:downcast:0» callableTypeDefIR) with | some «exec:1» => (let «eval:0» : SpecTec.externMethodTypeDefIR := «exec:1»; (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := «eval:0»; (.bind (.guard (((«exec:match:externMethodTypeDefIR:EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» externMethodTypeDefIR) = true))) (fun (_ : Unit) => (match externMethodTypeDefIR with | .«EXTERN_METHOD % `< % ',' % `> `( % `) ':' %» «exec:2» «exec:3» «exec:4» «exec:5» «exec:6» => (let _nameIR : nameIR := «exec:2»; (let «typeParameterIR_expl*» : (_root_.List typeParameterIR) := «exec:3»; (let «typeParameterIR_impl*» : (_root_.List typeParameterIR) := «exec:4»; (let «_parameterIR*» : (_root_.List parameterIR) := «exec:5»; (let _typeIR : typeIR := «exec:6»; (.pure (((«typeParameterIR_expl*», «typeParameterIR_impl*») : ((_root_.List typeParameterIR) × (_root_.List typeParameterIR)))))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$typeParameterListIR_of_callableTypeDefIR:clause:4» (input0 : SpecTec.callableTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTypeDefIR : SpecTec.callableTypeDefIR := input0; (.bind (.guard (((«sub:callableTypeDefIR:externMethodTypeDefIR» callableTypeDefIR) = true))) (fun (_ : Unit) => (match («$typeParameterListIR_of_callableTypeDefIR:case_5:downcast:0» callableTypeDefIR) with | some «exec:1» => (let «eval:0» : SpecTec.externMethodTypeDefIR := «exec:1»; (let externMethodTypeDefIR : SpecTec.externMethodTypeDefIR := «eval:0»; (.bind (.guard (((«exec:match:externMethodTypeDefIR:EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» externMethodTypeDefIR) = true))) (fun (_ : Unit) => (match externMethodTypeDefIR with | .«EXTERN_METHOD ABSTRACT % `< % ',' % `> `( % `) ':' %» «exec:2» «exec:3» «exec:4» «exec:5» «exec:6» => (let _nameIR : nameIR := «exec:2»; (let «typeParameterIR_expl*» : (_root_.List typeParameterIR) := «exec:3»; (let «typeParameterIR_impl*» : (_root_.List typeParameterIR) := «exec:4»; (let «_parameterIR*» : (_root_.List parameterIR) := «exec:5»; (let _typeIR : typeIR := «exec:6»; (.pure (((«typeParameterIR_expl*», «typeParameterIR_impl*») : ((_root_.List typeParameterIR) × (_root_.List typeParameterIR)))))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$typeParameterListIR_of_callableTypeDefIR:clause:5» (input0 : SpecTec.callableTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTypeDefIR : SpecTec.callableTypeDefIR := input0; (.bind (.guard (((«sub:callableTypeDefIR:parserApplyMethodTypeIR» callableTypeDefIR) = true))) (fun (_ : Unit) => (match («$typeParameterListIR_of_callableTypeDefIR:case_6:downcast:0» callableTypeDefIR) with | some «exec:1» => (let «eval:0» : SpecTec.parserApplyMethodTypeDefIR := «exec:1»; (let parserApplyMethodTypeDefIR : SpecTec.parserApplyMethodTypeDefIR := «eval:0»; (.pure (((([] : (_root_.List typeParameterIR)), ([] : (_root_.List typeParameterIR))) : ((_root_.List typeParameterIR) × (_root_.List typeParameterIR))))))) | none => .unmatch))))


noncomputable def «$typeParameterListIR_of_callableTypeDefIR:clause:6» (input0 : SpecTec.callableTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTypeDefIR : SpecTec.callableTypeDefIR := input0; (.bind (.guard (((«sub:callableTypeDefIR:controlApplyMethodTypeIR» callableTypeDefIR) = true))) (fun (_ : Unit) => (match («$typeParameterListIR_of_callableTypeDefIR:case_7:downcast:0» callableTypeDefIR) with | some «exec:1» => (let «eval:0» : SpecTec.controlApplyMethodTypeDefIR := «exec:1»; (let controlApplyMethodTypeDefIR : SpecTec.controlApplyMethodTypeDefIR := «eval:0»; (.pure (((([] : (_root_.List typeParameterIR)), ([] : (_root_.List typeParameterIR))) : ((_root_.List typeParameterIR) × (_root_.List typeParameterIR))))))) | none => .unmatch))))


noncomputable def «$typeParameterListIR_of_callableTypeDefIR_clauses» (input0 : callableTypeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$typeParameterListIR_of_callableTypeDefIR:clause:0»  input0), fun (_ : _root_.Unit) => («$typeParameterListIR_of_callableTypeDefIR:clause:1»  input0), fun (_ : _root_.Unit) => («$typeParameterListIR_of_callableTypeDefIR:clause:2»  input0), fun (_ : _root_.Unit) => («$typeParameterListIR_of_callableTypeDefIR:clause:3»  input0), fun (_ : _root_.Unit) => («$typeParameterListIR_of_callableTypeDefIR:clause:4»  input0), fun (_ : _root_.Unit) => («$typeParameterListIR_of_callableTypeDefIR:clause:5»  input0), fun (_ : _root_.Unit) => («$typeParameterListIR_of_callableTypeDefIR:clause:6»  input0)]


noncomputable def «$is_static_callableTypeIR:clause:0» (input0 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTypeIR : SpecTec.callableTypeIR := input0; (.bind (.guard (((«sub:callableTypeIR:externFunctionTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$is_static_callableTypeIR:case_1:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : externFunctionTypeIR := «exec:1»; (match «eval:0» with | .«EXTERN_FUNCTION % `( % `) ':' %» «exec:2» «exec:3» «exec:4» => (let t : _root_.String := «exec:2»; (let «_parameterIR*» : (_root_.List parameterIR) := «exec:3»; (let _typeIR : typeIR := «exec:4»; (.bind (.guard ("static_assert" = t)) (fun (_ : Unit) => (.pure ((((ctk.LCTK) : ctk) : ctk)))))))))) | none => .unmatch))))


noncomputable def «$is_static_callableTypeIR:clause:1» (input0 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTypeIR : SpecTec.callableTypeIR := input0; (.bind (.guard (((«sub:callableTypeIR:builtinSizeMethodTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$is_static_callableTypeIR:case_2:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : SpecTec.builtinSizeMethodTypeIR := «exec:1»; (let builtinSizeMethodTypeIR : SpecTec.builtinSizeMethodTypeIR := «eval:0»; (.pure ((((ctk.LCTK) : ctk) : ctk))))) | none => .unmatch))))


noncomputable def «$is_static_callableTypeIR:clause:2» (input0 : callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _callableTypeIR : callableTypeIR := input0; (.pure ((((ctk.DYN) : ctk) : ctk))))


noncomputable def «$is_static_callableTypeIR_clauses» (input0 : callableTypeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_static_callableTypeIR:clause:0»  input0), fun (_ : _root_.Unit) => («$is_static_callableTypeIR:clause:1»  input0), fun (_ : _root_.Unit) => («$is_static_callableTypeIR:clause:2»  input0)]


noncomputable def «$is_static_assert_callableTypeIR:clause:0» (input0 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTypeIR : SpecTec.callableTypeIR := input0; (.bind (.guard (((«sub:callableTypeIR:externFunctionTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$is_static_assert_callableTypeIR:case_1:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : externFunctionTypeIR := «exec:1»; (match «eval:0» with | .«EXTERN_FUNCTION % `( % `) ':' %» «exec:2» «exec:3» «exec:4» => (let t : _root_.String := «exec:2»; (let «_parameterIR*» : (_root_.List parameterIR) := «exec:3»; (let _typeIR : typeIR := «exec:4»; (.bind (.guard ("static_assert" = t)) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))))))) | none => .unmatch))))


noncomputable def «$is_static_assert_callableTypeIR:clause:1» (input0 : callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _callableTypeIR : callableTypeIR := input0; (.pure ((false : _root_.Bool))))


noncomputable def «$is_static_assert_callableTypeIR_clauses» (input0 : callableTypeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_static_assert_callableTypeIR:clause:0»  input0), fun (_ : _root_.Unit) => («$is_static_assert_callableTypeIR:clause:1»  input0)]


noncomputable def «$flatten_constOpt:clause:0» (input0 : SpecTec.constOpt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let constOpt : SpecTec.constOpt := input0; (.bind (.guard (((«exec:match:constOpt:_EMPTY» constOpt) = true))) (fun (_ : Unit) => (.pure ((((_root_.Option.none) : (_root_.Option const)) : (_root_.Option const)))))))


noncomputable def «$flatten_constOpt:clause:1» (input0 : SpecTec.constOpt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let constOpt : SpecTec.constOpt := input0; (.bind (.guard (((«sub:constOpt:const» constOpt) = true))) (fun (_ : Unit) => (match («$flatten_constOpt:case_2:downcast:0» constOpt) with | some «exec:1» => (let «eval:0» : SpecTec.const := «exec:1»; (let const : SpecTec.const := «eval:0»; (.pure (((_root_.Option.some const) : (_root_.Option SpecTec.const)))))) | none => .unmatch))))


noncomputable def «$flatten_constOpt_clauses» (input0 : constOpt) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_constOpt:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_constOpt:clause:1»  input0)]


noncomputable def «$parameterListIR_of_constructorDef:clause:0» (input0 : SpecTec.constructorDef) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let constructorDef : SpecTec.constructorDef := input0; (.bind (.guard (((«sub:constructorDef:externObjectConstructorDef» constructorDef) = true))) (fun (_ : Unit) => (match («$parameterListIR_of_constructorDef:case_1:downcast:0» constructorDef) with | some «exec:1» => (let «eval:0» : externObjectConstructorDef := «exec:1»; (match «eval:0» with | .«EXTERN % `< % `> `( % `) `{ % `}» «exec:2» «exec:3» «exec:4» «exec:5» => (let _nameIR : nameIR := «exec:2»; (let _typeParameterListIR : typeParameterListIR := «exec:3»; (let constructorParameterListIR : SpecTec.constructorParameterListIR := «exec:4»; (let _externMethodPrototypeListIR : externMethodPrototypeListIR := «exec:5»; (.pure ((constructorParameterListIR : (_root_.List parameterIR)))))))))) | none => .unmatch))))


noncomputable def «$parameterListIR_of_constructorDef:clause:1» (input0 : SpecTec.constructorDef) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let constructorDef : SpecTec.constructorDef := input0; (.bind (.guard (((«sub:constructorDef:parserObjectConstructorDef» constructorDef) = true))) (fun (_ : Unit) => (match («$parameterListIR_of_constructorDef:case_2:downcast:0» constructorDef) with | some «exec:1» => (let «eval:0» : parserObjectConstructorDef := «exec:1»; (match «eval:0» with | .«PARSER `< % `> `( % `) `( % `) `{ % % `}» «exec:2» «exec:3» «exec:4» «exec:5» «exec:6» => (let _typeParameterListIR : typeParameterListIR := «exec:2»; (let _parameterListIR : parameterListIR := «exec:3»; (let constructorParameterListIR : SpecTec.constructorParameterListIR := «exec:4»; (let _parserLocalDeclarationListIR : parserLocalDeclarationListIR := «exec:5»; (let _parserStateListIR : parserStateListIR := «exec:6»; (.pure ((constructorParameterListIR : (_root_.List parameterIR))))))))))) | none => .unmatch))))


noncomputable def «$parameterListIR_of_constructorDef:clause:2» (input0 : SpecTec.constructorDef) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let constructorDef : SpecTec.constructorDef := input0; (.bind (.guard (((«sub:constructorDef:controlObjectConstructorDef» constructorDef) = true))) (fun (_ : Unit) => (match («$parameterListIR_of_constructorDef:case_3:downcast:0» constructorDef) with | some «exec:1» => (let «eval:0» : controlObjectConstructorDef := «exec:1»; (match «eval:0» with | .«CONTROL `< % `> `( % `) `( % `) `{ % APPLY % `}» «exec:2» «exec:3» «exec:4» «exec:5» «exec:6» => (let _typeParameterListIR : typeParameterListIR := «exec:2»; (let _parameterListIR : parameterListIR := «exec:3»; (let constructorParameterListIR : SpecTec.constructorParameterListIR := «exec:4»; (let _controlLocalDeclarationListIR : controlLocalDeclarationListIR := «exec:5»; (let _controlBodyIR : controlBodyIR := «exec:6»; (.pure ((constructorParameterListIR : (_root_.List parameterIR))))))))))) | none => .unmatch))))


noncomputable def «$parameterListIR_of_constructorDef:clause:3» (input0 : SpecTec.constructorDef) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let constructorDef : SpecTec.constructorDef := input0; (.bind (.guard (((«sub:constructorDef:packageObjectConstructorDef» constructorDef) = true))) (fun (_ : Unit) => (match («$parameterListIR_of_constructorDef:case_4:downcast:0» constructorDef) with | some «exec:1» => (let «eval:0» : packageObjectConstructorDef := «exec:1»; (match «eval:0» with | .«PACKAGE `< % `> `( % `)» «exec:2» «exec:3» => (let _typeParameterListIR : typeParameterListIR := «exec:2»; (let constructorParameterListIR : SpecTec.constructorParameterListIR := «exec:3»; (.pure ((constructorParameterListIR : (_root_.List parameterIR)))))))) | none => .unmatch))))


noncomputable def «$parameterListIR_of_constructorDef_clauses» (input0 : constructorDef) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$parameterListIR_of_constructorDef:clause:0»  input0), fun (_ : _root_.Unit) => («$parameterListIR_of_constructorDef:clause:1»  input0), fun (_ : _root_.Unit) => («$parameterListIR_of_constructorDef:clause:2»  input0), fun (_ : _root_.Unit) => («$parameterListIR_of_constructorDef:clause:3»  input0)]


noncomputable def «$find_constructorDef_i:clause:0» (input0 : instContext) (input1 : SpecTec.prefixedNameIR) (input2 : (_root_.List argumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let IC : instContext := input0; (let prefixedNameIR : SpecTec.prefixedNameIR := input1; (let «argumentIR*» : (_root_.List argumentIR) := input2; (.bind (.guard (((«exec:match:prefixedNameIR:_BARE» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | ._BARE «exec:1» => (let nameIR : SpecTec.nameIR := «exec:1»; (.bind (.call ⟨SpecTec.callTargetKey, SpecTecCall.«$callTargetKey» nameIR «argumentIR*»⟩) (fun («exec:2» : SpecTec.callTargetKey) => (let «eval:0» : SpecTec.callTargetKey := «exec:2»; (let callTargetKey : SpecTec.callTargetKey := «eval:0»; (.bind (.call ⟨(_root_.Option (callResolution constructorDef)), SpecTecCall.«$find_overloaded» constructorDef (globalInstLayer.CONSTRUCTOR (instContext.GLOBAL IC)) callTargetKey SpecTecCall.«$parameterListIR_of_constructorDef»⟩) (fun («exec:3» : (_root_.Option (callResolution constructorDef))) => (let «eval:1» : (_root_.Option (callResolution constructorDef)) := «exec:3»; (.pure ((«eval:1» : (_root_.Option (callResolution constructorDef))))))))))))) | _ => .unmatch))))))


noncomputable def «$find_constructorDef_i:clause:1» (input0 : instContext) (input1 : SpecTec.prefixedNameIR) (input2 : (_root_.List argumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let IC : instContext := input0; (let prefixedNameIR : SpecTec.prefixedNameIR := input1; (let «argumentIR*» : (_root_.List argumentIR) := input2; (.bind (.guard (((«exec:match:prefixedNameIR:'.' %» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | .«'.' %» «exec:1» => (let nameIR : SpecTec.nameIR := «exec:1»; (.bind (.call ⟨SpecTec.callTargetKey, SpecTecCall.«$callTargetKey» nameIR «argumentIR*»⟩) (fun («exec:2» : SpecTec.callTargetKey) => (let «eval:0» : SpecTec.callTargetKey := «exec:2»; (let callTargetKey : SpecTec.callTargetKey := «eval:0»; (.bind (.call ⟨(_root_.Option (callResolution constructorDef)), SpecTecCall.«$find_overloaded» constructorDef (globalInstLayer.CONSTRUCTOR (instContext.GLOBAL IC)) callTargetKey SpecTecCall.«$parameterListIR_of_constructorDef»⟩) (fun («exec:3» : (_root_.Option (callResolution constructorDef))) => (let «eval:1» : (_root_.Option (callResolution constructorDef)) := «exec:3»; (.pure ((«eval:1» : (_root_.Option (callResolution constructorDef))))))))))))) | _ => .unmatch))))))


noncomputable def «$find_constructorDef_i_clauses» (input0 : instContext) (input1 : prefixedNameIR) (input2 : (_root_.List argumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_constructorDef_i:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$find_constructorDef_i:clause:1»  input0 input1 input2)]


noncomputable def «$find_constructorDef_e:clause:0» (input0 : evalContext) (input1 : SpecTec.prefixedNameIR) (input2 : (_root_.List argumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let EC : evalContext := input0; (let prefixedNameIR : SpecTec.prefixedNameIR := input1; (let «argumentIR*» : (_root_.List argumentIR) := input2; (.bind (.guard (((«exec:match:prefixedNameIR:_BARE» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | ._BARE «exec:1» => (let nameIR : SpecTec.nameIR := «exec:1»; (.bind (.call ⟨SpecTec.callTargetKey, SpecTecCall.«$callTargetKey» nameIR «argumentIR*»⟩) (fun («exec:2» : SpecTec.callTargetKey) => (let «eval:0» : SpecTec.callTargetKey := «exec:2»; (let callTargetKey : SpecTec.callTargetKey := «eval:0»; (.bind (.call ⟨(_root_.Option (callResolution constructorDef)), SpecTecCall.«$find_overloaded» constructorDef (globalInstLayer.CONSTRUCTOR (evalContext.GLOBAL EC)) callTargetKey SpecTecCall.«$parameterListIR_of_constructorDef»⟩) (fun («exec:3» : (_root_.Option (callResolution constructorDef))) => (let «eval:1» : (_root_.Option (callResolution constructorDef)) := «exec:3»; (.pure ((«eval:1» : (_root_.Option (callResolution constructorDef))))))))))))) | _ => .unmatch))))))


noncomputable def «$find_constructorDef_e:clause:1» (input0 : evalContext) (input1 : SpecTec.prefixedNameIR) (input2 : (_root_.List argumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let EC : evalContext := input0; (let prefixedNameIR : SpecTec.prefixedNameIR := input1; (let «argumentIR*» : (_root_.List argumentIR) := input2; (.bind (.guard (((«exec:match:prefixedNameIR:'.' %» prefixedNameIR) = true))) (fun (_ : Unit) => (match prefixedNameIR with | .«'.' %» «exec:1» => (let nameIR : SpecTec.nameIR := «exec:1»; (.bind (.call ⟨SpecTec.callTargetKey, SpecTecCall.«$callTargetKey» nameIR «argumentIR*»⟩) (fun («exec:2» : SpecTec.callTargetKey) => (let «eval:0» : SpecTec.callTargetKey := «exec:2»; (let callTargetKey : SpecTec.callTargetKey := «eval:0»; (.bind (.call ⟨(_root_.Option (callResolution constructorDef)), SpecTecCall.«$find_overloaded» constructorDef (globalInstLayer.CONSTRUCTOR (evalContext.GLOBAL EC)) callTargetKey SpecTecCall.«$parameterListIR_of_constructorDef»⟩) (fun («exec:3» : (_root_.Option (callResolution constructorDef))) => (let «eval:1» : (_root_.Option (callResolution constructorDef)) := «exec:3»; (.pure ((«eval:1» : (_root_.Option (callResolution constructorDef))))))))))))) | _ => .unmatch))))))


noncomputable def «$find_constructorDef_e_clauses» (input0 : evalContext) (input1 : prefixedNameIR) (input2 : (_root_.List argumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_constructorDef_e:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$find_constructorDef_e:clause:1»  input0 input1 input2)]


noncomputable def «$flatten_expressionList:clause:0» (input0 : SpecTec.expressionList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let expressionList : SpecTec.expressionList := input0; (.bind (.guard (((«exec:match:expressionList:_EMPTY» expressionList) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List expression)) : (_root_.List expression)))))))


noncomputable def «$flatten_expressionList:clause:1» (input0 : SpecTec.expressionList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let expressionList : SpecTec.expressionList := input0; (.bind (.guard (((«sub:expressionList:expression» expressionList) = true))) (fun (_ : Unit) => (match («$flatten_expressionList:case_2:downcast:0» expressionList) with | some «exec:1» => (let «eval:0» : SpecTec.expression := «exec:1»; (let expression : SpecTec.expression := «eval:0»; (.pure ((([expression] : (_root_.List SpecTec.expression)) : (_root_.List SpecTec.expression)))))) | none => .unmatch))))


noncomputable def «$flatten_expressionList:clause:2» (input0 : SpecTec.expressionList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let expressionList' : SpecTec.expressionList := input0; (.bind (.guard (((«exec:match:expressionList:% ',' %» expressionList') = true))) (fun (_ : Unit) => (match expressionList' with | .«% ',' %» «exec:1» «exec:2» => (let expressionList : SpecTec.expressionList := «exec:1»; (let expression : SpecTec.expression := «exec:2»; (.bind (.call ⟨(_root_.List SpecTec.expression), SpecTecCall.«$flatten_expressionList» expressionList⟩) (fun («exec:3» : (_root_.List SpecTec.expression)) => (let «eval:0» : (_root_.List SpecTec.expression) := «exec:3»; (.pure (((«eval:0» ++ ([expression] : (_root_.List SpecTec.expression))) : (_root_.List SpecTec.expression))))))))) | _ => .unmatch))))


noncomputable def «$flatten_expressionList_clauses» (input0 : expressionList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_expressionList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_expressionList:clause:1»  input0), fun (_ : _root_.Unit) => («$flatten_expressionList:clause:2»  input0)]


noncomputable def «$is_externConstructorPrototype:clause:0» (input0 : SpecTec.externConstructorOrMethodPrototype) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externConstructorOrMethodPrototype : SpecTec.externConstructorOrMethodPrototype := input0; (.bind (.guard (((«sub:externConstructorOrMethodPrototype:externConstructorPrototype» externConstructorOrMethodPrototype) = true))) (fun (_ : Unit) => (match («$is_externConstructorPrototype:case_1:downcast:0» externConstructorOrMethodPrototype) with | some «exec:1» => (let «eval:0» : SpecTec.externConstructorPrototype := «exec:1»; (let externConstructorPrototype : SpecTec.externConstructorPrototype := «eval:0»; (.pure ((true : _root_.Bool))))) | none => .unmatch))))

end SpecTec
