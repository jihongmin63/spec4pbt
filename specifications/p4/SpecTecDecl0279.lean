import SpecTecDecl0278

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$subst_parameterIR':clause:0» (input0 : SpecTec.theta) (input1 : parameterIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | .«% % % % %» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let annotationList : SpecTec.annotationList := «exec:1»; (let direction : SpecTec.direction := «exec:2»; (let typeIR : SpecTec.typeIR := «exec:3»; (let id : SpecTec.id := «exec:4»; (let parameterInitializerOptIR : SpecTec.parameterInitializerOptIR := «exec:5»; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$subst_typeIR'» theta typeIR⟩) (fun («exec:6» : SpecTec.typeIR) => (let «eval:0» : SpecTec.typeIR := «exec:6»; (let typeIR_subst : SpecTec.typeIR := «eval:0»; (.pure ((((parameterIR.«% % % % %» annotationList direction typeIR_subst id parameterInitializerOptIR) : parameterIR) : parameterIR))))))))))))))


noncomputable def «$subst_parameterIR'_clauses» (input0 : theta) (input1 : parameterIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_parameterIR':clause:0»  input0 input1)]


noncomputable def «$subst_callableTypeIR':clause:0» (input0 : SpecTec.theta) (input1 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (let callableTypeIR : SpecTec.callableTypeIR := input1; (.bind (.guard (((«sub:callableTypeIR:actionTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$subst_callableTypeIR':case_1:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : actionTypeIR := «exec:1»; (match «eval:0» with | .«% ACTION % `( % `)» «exec:2» «exec:3» «exec:4» => (let annotationList : SpecTec.annotationList := «exec:2»; (let nameIR : SpecTec.nameIR := «exec:3»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:4»; (.bind (.call ⟨(_root_.List parameterIR), SpecTecCall.«$subst_callableTypeIR':case_1:iter:1» theta «parameterIR*»⟩) (fun («exec:5» : (_root_.List parameterIR)) => (let «parameterIR_subst*» : (_root_.List parameterIR) := «exec:5»; (.pure ((((SpecTec.callableTypeIR.«% ACTION % `( % `)» annotationList nameIR «parameterIR_subst*») : SpecTec.callableTypeIR) : SpecTec.callableTypeIR))))))))))) | none => .unmatch)))))


noncomputable def «$subst_callableTypeIR':clause:1» (input0 : SpecTec.theta) (input1 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (let callableTypeIR : SpecTec.callableTypeIR := input1; (.bind (.guard (((«sub:callableTypeIR:definedFunctionTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$subst_callableTypeIR':case_2:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : definedFunctionTypeIR := «exec:1»; (match «eval:0» with | .«FUNCTION % `( % `) ':' %» «exec:2» «exec:3» «exec:4» => (let nameIR : SpecTec.nameIR := «exec:2»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:3»; (let typeIR : SpecTec.typeIR := «exec:4»; (.bind (.call ⟨(_root_.List parameterIR), SpecTecCall.«$subst_callableTypeIR':case_2:iter:1» theta «parameterIR*»⟩) (fun («exec:5» : (_root_.List parameterIR)) => (let «parameterIR_subst*» : (_root_.List parameterIR) := «exec:5»; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$subst_typeIR'» theta typeIR⟩) (fun («exec:6» : SpecTec.typeIR) => (let «eval:3» : SpecTec.typeIR := «exec:6»; (let typeIR_subst : SpecTec.typeIR := «eval:3»; (.pure ((((SpecTec.callableTypeIR.«FUNCTION % `( % `) ':' %» nameIR «parameterIR_subst*» typeIR_subst) : SpecTec.callableTypeIR) : SpecTec.callableTypeIR))))))))))))))) | none => .unmatch)))))


noncomputable def «$subst_callableTypeIR':clause:2» (input0 : SpecTec.theta) (input1 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (let callableTypeIR : SpecTec.callableTypeIR := input1; (.bind (.guard (((«sub:callableTypeIR:externFunctionTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$subst_callableTypeIR':case_3:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : externFunctionTypeIR := «exec:1»; (match «eval:0» with | .«EXTERN_FUNCTION % `( % `) ':' %» «exec:2» «exec:3» «exec:4» => (let nameIR : SpecTec.nameIR := «exec:2»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:3»; (let typeIR : SpecTec.typeIR := «exec:4»; (.bind (.call ⟨(_root_.List parameterIR), SpecTecCall.«$subst_callableTypeIR':case_3:iter:1» theta «parameterIR*»⟩) (fun («exec:5» : (_root_.List parameterIR)) => (let «parameterIR_subst*» : (_root_.List parameterIR) := «exec:5»; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$subst_typeIR'» theta typeIR⟩) (fun («exec:6» : SpecTec.typeIR) => (let «eval:3» : SpecTec.typeIR := «exec:6»; (let typeIR_subst : SpecTec.typeIR := «eval:3»; (.pure ((((SpecTec.callableTypeIR.«EXTERN_FUNCTION % `( % `) ':' %» nameIR «parameterIR_subst*» typeIR_subst) : SpecTec.callableTypeIR) : SpecTec.callableTypeIR))))))))))))))) | none => .unmatch)))))


noncomputable def «$subst_callableTypeIR':clause:3» (input0 : SpecTec.theta) (input1 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (let callableTypeIR : SpecTec.callableTypeIR := input1; (.bind (.guard (((«sub:callableTypeIR:builtinMethodTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$subst_callableTypeIR':case_4:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : SpecTec.builtinMethodTypeIR := «exec:1»; (let builtinMethodTypeIR : SpecTec.builtinMethodTypeIR := «eval:0»; (.pure (((«cast:builtinMethodTypeIR:callableTypeIR» builtinMethodTypeIR) : SpecTec.callableTypeIR))))) | none => .unmatch)))))


noncomputable def «$subst_callableTypeIR':clause:4» (input0 : SpecTec.theta) (input1 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (let callableTypeIR : SpecTec.callableTypeIR := input1; (.bind (.guard (((«sub:callableTypeIR:externMethodTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$subst_callableTypeIR':case_5:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : SpecTec.externMethodTypeIR := «exec:1»; (let externMethodTypeIR : SpecTec.externMethodTypeIR := «eval:0»; (.bind (.guard (((«exec:match:externMethodTypeIR:EXTERN_METHOD % `( % `) ':' %» externMethodTypeIR) = true))) (fun (_ : Unit) => (match externMethodTypeIR with | .«EXTERN_METHOD % `( % `) ':' %» «exec:2» «exec:3» «exec:4» => (let nameIR : SpecTec.nameIR := «exec:2»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:3»; (let typeIR : SpecTec.typeIR := «exec:4»; (.bind (.call ⟨(_root_.List parameterIR), SpecTecCall.«$subst_callableTypeIR':case_5:iter:1» theta «parameterIR*»⟩) (fun («exec:5» : (_root_.List parameterIR)) => (let «parameterIR_subst*» : (_root_.List parameterIR) := «exec:5»; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$subst_typeIR'» theta typeIR⟩) (fun («exec:6» : SpecTec.typeIR) => (let «eval:3» : SpecTec.typeIR := «exec:6»; (let typeIR_subst : SpecTec.typeIR := «eval:3»; (.pure ((((SpecTec.callableTypeIR.«EXTERN_METHOD % `( % `) ':' %» nameIR «parameterIR_subst*» typeIR_subst) : SpecTec.callableTypeIR) : SpecTec.callableTypeIR))))))))))))) | _ => .unmatch))))) | none => .unmatch)))))


noncomputable def «$subst_callableTypeIR':clause:5» (input0 : SpecTec.theta) (input1 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (let callableTypeIR : SpecTec.callableTypeIR := input1; (.bind (.guard (((«sub:callableTypeIR:externMethodTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$subst_callableTypeIR':case_6:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : SpecTec.externMethodTypeIR := «exec:1»; (let externMethodTypeIR : SpecTec.externMethodTypeIR := «eval:0»; (.bind (.guard (((«exec:match:externMethodTypeIR:EXTERN_METHOD ABSTRACT % `( % `) ':' %» externMethodTypeIR) = true))) (fun (_ : Unit) => (match externMethodTypeIR with | .«EXTERN_METHOD ABSTRACT % `( % `) ':' %» «exec:2» «exec:3» «exec:4» => (let nameIR : SpecTec.nameIR := «exec:2»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:3»; (let typeIR : SpecTec.typeIR := «exec:4»; (.bind (.call ⟨(_root_.List parameterIR), SpecTecCall.«$subst_callableTypeIR':case_6:iter:1» theta «parameterIR*»⟩) (fun («exec:5» : (_root_.List parameterIR)) => (let «parameterIR_subst*» : (_root_.List parameterIR) := «exec:5»; (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$subst_typeIR'» theta typeIR⟩) (fun («exec:6» : SpecTec.typeIR) => (let «eval:3» : SpecTec.typeIR := «exec:6»; (let typeIR_subst : SpecTec.typeIR := «eval:3»; (.pure ((((SpecTec.callableTypeIR.«EXTERN_METHOD ABSTRACT % `( % `) ':' %» nameIR «parameterIR_subst*» typeIR_subst) : SpecTec.callableTypeIR) : SpecTec.callableTypeIR))))))))))))) | _ => .unmatch))))) | none => .unmatch)))))


noncomputable def «$subst_callableTypeIR':clause:6» (input0 : SpecTec.theta) (input1 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (let callableTypeIR : SpecTec.callableTypeIR := input1; (.bind (.guard (((«sub:callableTypeIR:parserApplyMethodTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$subst_callableTypeIR':case_7:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : parserApplyMethodTypeIR := «exec:1»; (match «eval:0» with | .«PARSER_APPLY `( % `)» «exec:2» => (let «parameterIR*» : (_root_.List parameterIR) := «exec:2»; (.bind (.call ⟨(_root_.List parameterIR), SpecTecCall.«$subst_callableTypeIR':case_7:iter:1» theta «parameterIR*»⟩) (fun («exec:3» : (_root_.List parameterIR)) => (let «parameterIR_subst*» : (_root_.List parameterIR) := «exec:3»; (.pure ((((SpecTec.callableTypeIR.«PARSER_APPLY `( % `)» «parameterIR_subst*») : SpecTec.callableTypeIR) : SpecTec.callableTypeIR))))))))) | none => .unmatch)))))


noncomputable def «$subst_callableTypeIR':clause:7» (input0 : SpecTec.theta) (input1 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (let callableTypeIR : SpecTec.callableTypeIR := input1; (.bind (.guard (((«sub:callableTypeIR:controlApplyMethodTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$subst_callableTypeIR':case_8:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : controlApplyMethodTypeIR := «exec:1»; (match «eval:0» with | .«CONTROL_APPLY `( % `)» «exec:2» => (let «parameterIR*» : (_root_.List parameterIR) := «exec:2»; (.bind (.call ⟨(_root_.List parameterIR), SpecTecCall.«$subst_callableTypeIR':case_8:iter:1» theta «parameterIR*»⟩) (fun («exec:3» : (_root_.List parameterIR)) => (let «parameterIR_subst*» : (_root_.List parameterIR) := «exec:3»; (.pure ((((SpecTec.callableTypeIR.«CONTROL_APPLY `( % `)» «parameterIR_subst*») : SpecTec.callableTypeIR) : SpecTec.callableTypeIR))))))))) | none => .unmatch)))))


noncomputable def «$subst_callableTypeIR':clause:8» (input0 : SpecTec.theta) (input1 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (let callableTypeIR : SpecTec.callableTypeIR := input1; (.bind (.guard (((«sub:callableTypeIR:tableApplyMethodTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$subst_callableTypeIR':case_9:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : SpecTec.tableApplyMethodTypeIR := «exec:1»; (let tableApplyMethodTypeIR : SpecTec.tableApplyMethodTypeIR := «eval:0»; (.pure (((«cast:tableApplyMethodTypeIR:callableTypeIR» tableApplyMethodTypeIR) : SpecTec.callableTypeIR))))) | none => .unmatch)))))


noncomputable def «$subst_callableTypeIR'_clauses» (input0 : theta) (input1 : callableTypeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_callableTypeIR':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_callableTypeIR':clause:1»  input0 input1), fun (_ : _root_.Unit) => («$subst_callableTypeIR':clause:2»  input0 input1), fun (_ : _root_.Unit) => («$subst_callableTypeIR':clause:3»  input0 input1), fun (_ : _root_.Unit) => («$subst_callableTypeIR':clause:4»  input0 input1), fun (_ : _root_.Unit) => («$subst_callableTypeIR':clause:5»  input0 input1), fun (_ : _root_.Unit) => («$subst_callableTypeIR':clause:6»  input0 input1), fun (_ : _root_.Unit) => («$subst_callableTypeIR':clause:7»  input0 input1), fun (_ : _root_.Unit) => («$subst_callableTypeIR':clause:8»  input0 input1)]


noncomputable def «$subst_callableTypeIR':case_1:iter:1:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List parameterIR)) : (_root_.List parameterIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_callableTypeIR':case_1:iter:1:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨SpecTec.parameterIR, SpecTecCall.«$subst_parameterIR'» theta parameterIR⟩) (fun («exec:3» : SpecTec.parameterIR) => (let «eval:2» : SpecTec.parameterIR := «exec:3»; (let parameterIR_subst : SpecTec.parameterIR := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.parameterIR), SpecTecCall.«$subst_callableTypeIR':case_1:iter:1» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.parameterIR)) => (let «tail:1» : (_root_.List SpecTec.parameterIR) := «exec:4»; (.pure (((parameterIR_subst :: «tail:1») : (_root_.List SpecTec.parameterIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_callableTypeIR':case_1:iter:1_clauses» (input0 : theta) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_callableTypeIR':case_1:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_callableTypeIR':case_1:iter:1:clause:1»  input0 input1)]


noncomputable def «$subst_callableTypeIR':case_2:iter:1:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List parameterIR)) : (_root_.List parameterIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_callableTypeIR':case_2:iter:1:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨SpecTec.parameterIR, SpecTecCall.«$subst_parameterIR'» theta parameterIR⟩) (fun («exec:3» : SpecTec.parameterIR) => (let «eval:2» : SpecTec.parameterIR := «exec:3»; (let parameterIR_subst : SpecTec.parameterIR := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.parameterIR), SpecTecCall.«$subst_callableTypeIR':case_2:iter:1» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.parameterIR)) => (let «tail:1» : (_root_.List SpecTec.parameterIR) := «exec:4»; (.pure (((parameterIR_subst :: «tail:1») : (_root_.List SpecTec.parameterIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_callableTypeIR':case_2:iter:1_clauses» (input0 : theta) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_callableTypeIR':case_2:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_callableTypeIR':case_2:iter:1:clause:1»  input0 input1)]


noncomputable def «$subst_callableTypeIR':case_3:iter:1:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List parameterIR)) : (_root_.List parameterIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_callableTypeIR':case_3:iter:1:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨SpecTec.parameterIR, SpecTecCall.«$subst_parameterIR'» theta parameterIR⟩) (fun («exec:3» : SpecTec.parameterIR) => (let «eval:2» : SpecTec.parameterIR := «exec:3»; (let parameterIR_subst : SpecTec.parameterIR := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.parameterIR), SpecTecCall.«$subst_callableTypeIR':case_3:iter:1» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.parameterIR)) => (let «tail:1» : (_root_.List SpecTec.parameterIR) := «exec:4»; (.pure (((parameterIR_subst :: «tail:1») : (_root_.List SpecTec.parameterIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_callableTypeIR':case_3:iter:1_clauses» (input0 : theta) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_callableTypeIR':case_3:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_callableTypeIR':case_3:iter:1:clause:1»  input0 input1)]


noncomputable def «$subst_callableTypeIR':case_5:iter:1:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List parameterIR)) : (_root_.List parameterIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_callableTypeIR':case_5:iter:1:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨SpecTec.parameterIR, SpecTecCall.«$subst_parameterIR'» theta parameterIR⟩) (fun («exec:3» : SpecTec.parameterIR) => (let «eval:2» : SpecTec.parameterIR := «exec:3»; (let parameterIR_subst : SpecTec.parameterIR := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.parameterIR), SpecTecCall.«$subst_callableTypeIR':case_5:iter:1» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.parameterIR)) => (let «tail:1» : (_root_.List SpecTec.parameterIR) := «exec:4»; (.pure (((parameterIR_subst :: «tail:1») : (_root_.List SpecTec.parameterIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_callableTypeIR':case_5:iter:1_clauses» (input0 : theta) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_callableTypeIR':case_5:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_callableTypeIR':case_5:iter:1:clause:1»  input0 input1)]


noncomputable def «$subst_callableTypeIR':case_6:iter:1:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List parameterIR)) : (_root_.List parameterIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_callableTypeIR':case_6:iter:1:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨SpecTec.parameterIR, SpecTecCall.«$subst_parameterIR'» theta parameterIR⟩) (fun («exec:3» : SpecTec.parameterIR) => (let «eval:2» : SpecTec.parameterIR := «exec:3»; (let parameterIR_subst : SpecTec.parameterIR := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.parameterIR), SpecTecCall.«$subst_callableTypeIR':case_6:iter:1» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.parameterIR)) => (let «tail:1» : (_root_.List SpecTec.parameterIR) := «exec:4»; (.pure (((parameterIR_subst :: «tail:1») : (_root_.List SpecTec.parameterIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_callableTypeIR':case_6:iter:1_clauses» (input0 : theta) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_callableTypeIR':case_6:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_callableTypeIR':case_6:iter:1:clause:1»  input0 input1)]


noncomputable def «$subst_callableTypeIR':case_7:iter:1:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List parameterIR)) : (_root_.List parameterIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_callableTypeIR':case_7:iter:1:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨SpecTec.parameterIR, SpecTecCall.«$subst_parameterIR'» theta parameterIR⟩) (fun («exec:3» : SpecTec.parameterIR) => (let «eval:2» : SpecTec.parameterIR := «exec:3»; (let parameterIR_subst : SpecTec.parameterIR := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.parameterIR), SpecTecCall.«$subst_callableTypeIR':case_7:iter:1» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.parameterIR)) => (let «tail:1» : (_root_.List SpecTec.parameterIR) := «exec:4»; (.pure (((parameterIR_subst :: «tail:1») : (_root_.List SpecTec.parameterIR))))))))))))) | [] => .unmatch))


noncomputable def «$subst_callableTypeIR':case_7:iter:1_clauses» (input0 : theta) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$subst_callableTypeIR':case_7:iter:1:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$subst_callableTypeIR':case_7:iter:1:clause:1»  input0 input1)]


noncomputable def «$subst_callableTypeIR':case_8:iter:1:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | [] => (.pure ((([] : (_root_.List parameterIR)) : (_root_.List parameterIR)))) | _ :: _ => .unmatch))


noncomputable def «$subst_callableTypeIR':case_8:iter:1:clause:1» (input0 : SpecTec.theta) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (match input1 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨SpecTec.parameterIR, SpecTecCall.«$subst_parameterIR'» theta parameterIR⟩) (fun («exec:3» : SpecTec.parameterIR) => (let «eval:2» : SpecTec.parameterIR := «exec:3»; (let parameterIR_subst : SpecTec.parameterIR := «eval:2»; (.bind (.call ⟨(_root_.List SpecTec.parameterIR), SpecTecCall.«$subst_callableTypeIR':case_8:iter:1» theta «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.parameterIR)) => (let «tail:1» : (_root_.List SpecTec.parameterIR) := «exec:4»; (.pure (((parameterIR_subst :: «tail:1») : (_root_.List SpecTec.parameterIR))))))))))))) | [] => .unmatch))

end SpecTec
