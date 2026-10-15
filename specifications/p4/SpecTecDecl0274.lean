import SpecTecDecl0273

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$free_typeIR:case_17:iter:1:clause:1» (input0 : (_root_.List SpecTec.typeArgumentIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeArgumentIR⟩) (fun («exec:3» : bound) => (let «eval:2» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_17:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:2» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_17:iter:1_clauses» (input0 : (_root_.List typeArgumentIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_17:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_17:iter:1:clause:1»  input0)]


noncomputable def «$free_typeIR:case_17:iter:4:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_typeIR:case_17:iter:4:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeIR⟩) (fun («exec:3» : bound) => (let «eval:5» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_17:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:5» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_17:iter:4_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_17:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_17:iter:4:clause:1»  input0)]


noncomputable def «$free_typeIR:case_21:iter:1:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_typeIR:case_21:iter:1:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeIR⟩) (fun («exec:3» : bound) => (let «eval:2» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_21:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:2» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_21:iter:1_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_21:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_21:iter:1:clause:1»  input0)]


noncomputable def «$free_typeIR:case_22:iter:1:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_typeIR:case_22:iter:1:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeIR⟩) (fun («exec:3» : bound) => (let «eval:2» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_22:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:2» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_22:iter:1_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_22:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_22:iter:1:clause:1»  input0)]


noncomputable def «$free_typeIR:case_23:iter:3:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_typeIR:case_23:iter:3:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeIR⟩) (fun («exec:3» : bound) => (let «eval:4» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_23:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:4» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_23:iter:3_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_23:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_23:iter:3:clause:1»  input0)]


noncomputable def «$free_typeIR:case_24:iter:3:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_typeIR:case_24:iter:3:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeIR⟩) (fun («exec:3» : bound) => (let «eval:4» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_typeIR:case_24:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:4» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_typeIR:case_24:iter:3_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeIR:case_24:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$free_typeIR:case_24:iter:3:clause:1»  input0)]


noncomputable def «$free_parameterIR:clause:0» (input0 : parameterIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% % % % %» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:1»; (let _direction : direction := «exec:2»; (let typeIR : SpecTec.typeIR := «exec:3»; (let _id : id := «exec:4»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:5»; (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeIR⟩) (fun («exec:6» : bound) => (let «eval:0» : bound := «exec:6»; (.pure ((«eval:0» : bound))))))))))))


noncomputable def «$free_parameterIR_clauses» (input0 : parameterIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_parameterIR:clause:0»  input0)]


noncomputable def «$free_callableTypeIR:clause:0» (input0 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTypeIR : SpecTec.callableTypeIR := input0; (.bind (.guard (((«sub:callableTypeIR:actionTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$free_callableTypeIR:case_1:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : actionTypeIR := «exec:1»; (match «eval:0» with | .«% ACTION % `( % `)» «exec:2» «exec:3» «exec:4» => (let _annotationList : annotationList := «exec:2»; (let _nameIR : nameIR := «exec:3»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:4»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_1:iter:1» «parameterIR*»⟩) (fun («exec:5» : (_root_.List (set _root_.String))) => (let «eval:3» : (_root_.List bound) := «exec:5»; (let B_params : bound := («$unions_set» «eval:3»); (.pure ((B_params : bound)))))))))))) | none => .unmatch))))


noncomputable def «$free_callableTypeIR:clause:1» (input0 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTypeIR : SpecTec.callableTypeIR := input0; (.bind (.guard (((«sub:callableTypeIR:definedFunctionTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$free_callableTypeIR:case_2:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : definedFunctionTypeIR := «exec:1»; (match «eval:0» with | .«FUNCTION % `( % `) ':' %» «exec:2» «exec:3» «exec:4» => (let _nameIR : nameIR := «exec:2»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:3»; (let typeIR : SpecTec.typeIR := «exec:4»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_2:iter:1» «parameterIR*»⟩) (fun («exec:5» : (_root_.List (set _root_.String))) => (let «eval:3» : (_root_.List bound) := «exec:5»; (let B_params : bound := («$unions_set» «eval:3»); (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeIR⟩) (fun («exec:6» : bound) => (let «eval:4» : bound := «exec:6»; (let B_ret : bound := «eval:4»; (.pure (((«$union_set» B_params B_ret) : bound)))))))))))))))) | none => .unmatch))))


noncomputable def «$free_callableTypeIR:clause:2» (input0 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTypeIR : SpecTec.callableTypeIR := input0; (.bind (.guard (((«sub:callableTypeIR:externFunctionTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$free_callableTypeIR:case_3:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : externFunctionTypeIR := «exec:1»; (match «eval:0» with | .«EXTERN_FUNCTION % `( % `) ':' %» «exec:2» «exec:3» «exec:4» => (let _nameIR : nameIR := «exec:2»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:3»; (let typeIR : SpecTec.typeIR := «exec:4»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_3:iter:1» «parameterIR*»⟩) (fun («exec:5» : (_root_.List (set _root_.String))) => (let «eval:3» : (_root_.List bound) := «exec:5»; (let B_params : bound := («$unions_set» «eval:3»); (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeIR⟩) (fun («exec:6» : bound) => (let «eval:4» : bound := «exec:6»; (let B_ret : bound := «eval:4»; (.pure (((«$union_set» B_params B_ret) : bound)))))))))))))))) | none => .unmatch))))


noncomputable def «$free_callableTypeIR:clause:3» (input0 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTypeIR : SpecTec.callableTypeIR := input0; (.bind (.guard (((«sub:callableTypeIR:builtinMethodTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$free_callableTypeIR:case_4:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : SpecTec.builtinMethodTypeIR := «exec:1»; (let builtinMethodTypeIR : SpecTec.builtinMethodTypeIR := «eval:0»; (.pure ((((set.«`{ % `}» ([] : (_root_.List typeId))) : (set typeId)) : bound))))) | none => .unmatch))))


noncomputable def «$free_callableTypeIR:clause:4» (input0 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTypeIR : SpecTec.callableTypeIR := input0; (.bind (.guard (((«sub:callableTypeIR:externMethodTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$free_callableTypeIR:case_5:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : SpecTec.externMethodTypeIR := «exec:1»; (let externMethodTypeIR : SpecTec.externMethodTypeIR := «eval:0»; (.bind (.guard (((«exec:match:externMethodTypeIR:EXTERN_METHOD % `( % `) ':' %» externMethodTypeIR) = true))) (fun (_ : Unit) => (match externMethodTypeIR with | .«EXTERN_METHOD % `( % `) ':' %» «exec:2» «exec:3» «exec:4» => (let _nameIR : nameIR := «exec:2»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:3»; (let typeIR : SpecTec.typeIR := «exec:4»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_5:iter:1» «parameterIR*»⟩) (fun («exec:5» : (_root_.List (set _root_.String))) => (let «eval:3» : (_root_.List bound) := «exec:5»; (let B_params : bound := («$unions_set» «eval:3»); (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeIR⟩) (fun («exec:6» : bound) => (let «eval:4» : bound := «exec:6»; (let B_ret : bound := «eval:4»; (.pure (((«$union_set» B_params B_ret) : bound)))))))))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$free_callableTypeIR:clause:5» (input0 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTypeIR : SpecTec.callableTypeIR := input0; (.bind (.guard (((«sub:callableTypeIR:externMethodTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$free_callableTypeIR:case_6:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : SpecTec.externMethodTypeIR := «exec:1»; (let externMethodTypeIR : SpecTec.externMethodTypeIR := «eval:0»; (.bind (.guard (((«exec:match:externMethodTypeIR:EXTERN_METHOD ABSTRACT % `( % `) ':' %» externMethodTypeIR) = true))) (fun (_ : Unit) => (match externMethodTypeIR with | .«EXTERN_METHOD ABSTRACT % `( % `) ':' %» «exec:2» «exec:3» «exec:4» => (let _nameIR : nameIR := «exec:2»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:3»; (let typeIR : SpecTec.typeIR := «exec:4»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_6:iter:1» «parameterIR*»⟩) (fun («exec:5» : (_root_.List (set _root_.String))) => (let «eval:3» : (_root_.List bound) := «exec:5»; (let B_params : bound := («$unions_set» «eval:3»); (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeIR⟩) (fun («exec:6» : bound) => (let «eval:4» : bound := «exec:6»; (let B_ret : bound := «eval:4»; (.pure (((«$union_set» B_params B_ret) : bound)))))))))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$free_callableTypeIR:clause:6» (input0 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTypeIR : SpecTec.callableTypeIR := input0; (.bind (.guard (((«sub:callableTypeIR:parserApplyMethodTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$free_callableTypeIR:case_7:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : parserApplyMethodTypeIR := «exec:1»; (match «eval:0» with | .«PARSER_APPLY `( % `)» «exec:2» => (let «parameterIR*» : (_root_.List parameterIR) := «exec:2»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_7:iter:1» «parameterIR*»⟩) (fun («exec:3» : (_root_.List (set _root_.String))) => (let «eval:3» : (_root_.List bound) := «exec:3»; (let B_params : bound := («$unions_set» «eval:3»); (.pure ((B_params : bound)))))))))) | none => .unmatch))))


noncomputable def «$free_callableTypeIR:clause:7» (input0 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTypeIR : SpecTec.callableTypeIR := input0; (.bind (.guard (((«sub:callableTypeIR:controlApplyMethodTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$free_callableTypeIR:case_8:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : controlApplyMethodTypeIR := «exec:1»; (match «eval:0» with | .«CONTROL_APPLY `( % `)» «exec:2» => (let «parameterIR*» : (_root_.List parameterIR) := «exec:2»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_8:iter:1» «parameterIR*»⟩) (fun («exec:3» : (_root_.List (set _root_.String))) => (let «eval:3» : (_root_.List bound) := «exec:3»; (let B_params : bound := («$unions_set» «eval:3»); (.pure ((B_params : bound)))))))))) | none => .unmatch))))


noncomputable def «$free_callableTypeIR:clause:8» (input0 : SpecTec.callableTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTypeIR : SpecTec.callableTypeIR := input0; (.bind (.guard (((«sub:callableTypeIR:tableApplyMethodTypeIR» callableTypeIR) = true))) (fun (_ : Unit) => (match («$free_callableTypeIR:case_9:downcast:0» callableTypeIR) with | some «exec:1» => (let «eval:0» : tableApplyMethodTypeIR := «exec:1»; (match «eval:0» with | .«TABLE_APPLY ':' %» «exec:2» => (let _tableMetadataStructTypeIR : tableMetadataStructTypeIR := «exec:2»; (.pure ((((set.«`{ % `}» ([] : (_root_.List typeId))) : (set typeId)) : bound)))))) | none => .unmatch))))


noncomputable def «$free_callableTypeIR_clauses» (input0 : callableTypeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_callableTypeIR:clause:0»  input0), fun (_ : _root_.Unit) => («$free_callableTypeIR:clause:1»  input0), fun (_ : _root_.Unit) => («$free_callableTypeIR:clause:2»  input0), fun (_ : _root_.Unit) => («$free_callableTypeIR:clause:3»  input0), fun (_ : _root_.Unit) => («$free_callableTypeIR:clause:4»  input0), fun (_ : _root_.Unit) => («$free_callableTypeIR:clause:5»  input0), fun (_ : _root_.Unit) => («$free_callableTypeIR:clause:6»  input0), fun (_ : _root_.Unit) => («$free_callableTypeIR:clause:7»  input0), fun (_ : _root_.Unit) => («$free_callableTypeIR:clause:8»  input0)]


noncomputable def «$free_callableTypeIR:case_1:iter:1:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_callableTypeIR:case_1:iter:1:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_parameterIR» parameterIR⟩) (fun («exec:3» : bound) => (let «eval:2» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_1:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:2» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_callableTypeIR:case_1:iter:1_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_callableTypeIR:case_1:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$free_callableTypeIR:case_1:iter:1:clause:1»  input0)]

end SpecTec
