import SpecTecDecl0274

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$free_callableTypeIR:case_2:iter:1:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_callableTypeIR:case_2:iter:1:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_parameterIR» parameterIR⟩) (fun («exec:3» : bound) => (let «eval:2» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_2:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:2» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_callableTypeIR:case_2:iter:1_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_callableTypeIR:case_2:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$free_callableTypeIR:case_2:iter:1:clause:1»  input0)]


noncomputable def «$free_callableTypeIR:case_3:iter:1:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_callableTypeIR:case_3:iter:1:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_parameterIR» parameterIR⟩) (fun («exec:3» : bound) => (let «eval:2» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_3:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:2» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_callableTypeIR:case_3:iter:1_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_callableTypeIR:case_3:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$free_callableTypeIR:case_3:iter:1:clause:1»  input0)]


noncomputable def «$free_callableTypeIR:case_5:iter:1:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_callableTypeIR:case_5:iter:1:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_parameterIR» parameterIR⟩) (fun («exec:3» : bound) => (let «eval:2» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_5:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:2» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_callableTypeIR:case_5:iter:1_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_callableTypeIR:case_5:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$free_callableTypeIR:case_5:iter:1:clause:1»  input0)]


noncomputable def «$free_callableTypeIR:case_6:iter:1:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_callableTypeIR:case_6:iter:1:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_parameterIR» parameterIR⟩) (fun («exec:3» : bound) => (let «eval:2» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_6:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:2» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_callableTypeIR:case_6:iter:1_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_callableTypeIR:case_6:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$free_callableTypeIR:case_6:iter:1:clause:1»  input0)]


noncomputable def «$free_callableTypeIR:case_7:iter:1:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_callableTypeIR:case_7:iter:1:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_parameterIR» parameterIR⟩) (fun («exec:3» : bound) => (let «eval:2» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_7:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:2» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_callableTypeIR:case_7:iter:1_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_callableTypeIR:case_7:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$free_callableTypeIR:case_7:iter:1:clause:1»  input0)]


noncomputable def «$free_callableTypeIR:case_8:iter:1:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_callableTypeIR:case_8:iter:1:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_parameterIR» parameterIR⟩) (fun («exec:3» : bound) => (let «eval:2» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_callableTypeIR:case_8:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:2» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_callableTypeIR:case_8:iter:1_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_callableTypeIR:case_8:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$free_callableTypeIR:case_8:iter:1:clause:1»  input0)]


noncomputable def «$free_callableTypeDefIR:clause:0» (input0 : SpecTec.callableTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let callableTypeDefIR : SpecTec.callableTypeDefIR := input0; (.bind (.call ⟨((_root_.List typeParameterIR) × (_root_.List typeParameterIR)), SpecTecCall.«$typeParameterListIR_of_callableTypeDefIR» callableTypeDefIR⟩) (fun («exec:1» : ((_root_.List typeParameterIR) × (_root_.List typeParameterIR))) => (let «eval:0» : ((_root_.List typeParameterIR) × (_root_.List typeParameterIR)) := «exec:1»; (let «typeId_tparam_expl*» : (_root_.List typeId) := («eval:0»).1; (let «typeId_tparam_impl*» : (_root_.List typeId) := («eval:0»).2; (let B_tparams : bound := ((set.«`{ % `}» («typeId_tparam_expl*» ++ «typeId_tparam_impl*»)) : (set typeId)); (.bind (.call ⟨SpecTec.callableTypeIR, SpecTecCall.«$callableTypeIR_of_callableTypeDefIR» callableTypeDefIR⟩) (fun («exec:2» : SpecTec.callableTypeIR) => (let «eval:1» : SpecTec.callableTypeIR := «exec:2»; (let callableTypeIR : SpecTec.callableTypeIR := «eval:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_callableTypeIR» callableTypeIR⟩) (fun («exec:3» : bound) => (let «eval:2» : bound := «exec:3»; (let B_base : bound := «eval:2»; (.pure (((«$diff_set» B_base B_tparams) : bound))))))))))))))))))


noncomputable def «$free_callableTypeDefIR_clauses» (input0 : callableTypeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_callableTypeDefIR:clause:0»  input0)]


noncomputable def «$free_typeDefIR:clause:0» (input0 : SpecTec.typeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDefIR : SpecTec.typeDefIR := input0; (.bind (.call ⟨((_root_.List typeParameterIR) × (_root_.List typeParameterIR)), SpecTecCall.«$typeParameterListIR_of_typeDefIR» typeDefIR⟩) (fun («exec:1» : ((_root_.List typeParameterIR) × (_root_.List typeParameterIR))) => (let «eval:0» : ((_root_.List typeParameterIR) × (_root_.List typeParameterIR)) := «exec:1»; (let «typeParameterIR_expl*» : (_root_.List typeParameterIR) := («eval:0»).1; (let «typeParameterIR_impl*» : (_root_.List typeParameterIR) := («eval:0»).2; (let B_tparams : bound := ((set.«`{ % `}» («typeParameterIR_expl*» ++ «typeParameterIR_impl*»)) : (set typeId)); (.bind (.call ⟨SpecTec.typeIR, SpecTecCall.«$typeIR_of_typeDefIR» typeDefIR⟩) (fun («exec:2» : SpecTec.typeIR) => (let «eval:1» : SpecTec.typeIR := «exec:2»; (let typeIR : SpecTec.typeIR := «eval:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeIR⟩) (fun («exec:3» : bound) => (let «eval:2» : bound := «exec:3»; (let B_base : bound := «eval:2»; (.pure (((«$diff_set» B_base B_tparams) : bound))))))))))))))))))


noncomputable def «$free_typeDefIR_clauses» (input0 : typeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_typeDefIR:clause:0»  input0)]


noncomputable def «$free_parameterIRs:case_1:iter:0:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$free_parameterIRs:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_parameterIR» parameterIR⟩) (fun («exec:3» : bound) => (let «eval:1» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_parameterIRs:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:1» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$free_parameterIRs:case_1:iter:0_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_parameterIRs:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$free_parameterIRs:case_1:iter:0:clause:1»  input0)]


noncomputable def «$free_parameterIRs:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «parameterIR*» : (_root_.List parameterIR) := input0; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$free_parameterIRs:case_1:iter:0» «parameterIR*»⟩) (fun («exec:1» : (_root_.List (set _root_.String))) => (let «eval:2» : (_root_.List bound) := «exec:1»; (.pure (((«$unions_set» «eval:2») : bound)))))))


noncomputable def «$free_parameterIRs_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$free_parameterIRs:clause:0»  input0)]


noncomputable def «$capture_avoiding_:case_1:iter:4:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (set _root_.String))) : (_root_.List (set _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$capture_avoiding_:case_1:iter:4:clause:1» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR_free : typeIR := «exec:2»; (let «tail:0» : (_root_.List typeIR) := «exec:1»; (.bind (.call ⟨bound, SpecTecCall.«$free_typeIR» typeIR_free⟩) (fun («exec:3» : bound) => (let «eval:5» : bound := «exec:3»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$capture_avoiding_:case_1:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List (set _root_.String))) => (let «tail:1» : (_root_.List (set _root_.String)) := «exec:4»; (.pure (((«eval:5» :: «tail:1») : (_root_.List (set _root_.String))))))))))))) | [] => .unmatch)


noncomputable def «$capture_avoiding_:case_1:iter:4_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$capture_avoiding_:case_1:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («$capture_avoiding_:case_1:iter:4:clause:1»  input0)]


noncomputable def «$capture_avoiding_:clause:0» (input0 : SpecTec.theta) (input1 : (_root_.List typeParameterIR)) (input2 : bound) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let theta : SpecTec.theta := input0; (let «typeParameterIR*» : (_root_.List typeParameterIR) := input1; (let B : bound := input2; (match («$diff_set» B ((set.«`{ % `}» «typeParameterIR*») : (set typeId))) with | .«`{ % `}» «exec:1» => (let «typeId_free*» : (_root_.List typeId) := «exec:1»; (.bind (.call ⟨(_root_.List (_root_.Option typeIR)), SpecTecCall.«$capture_avoiding_:case_1:iter:0» theta «typeId_free*»⟩) (fun («exec:2» : (_root_.List (_root_.Option typeIR))) => (let «typeIR?*» : (_root_.List (_root_.Option typeIR)) := «exec:2»; (.bind (.call ⟨_root_.Unit, SpecTecCall.«$capture_avoiding_:case_1:iter:2» «typeIR?*»⟩) (fun («exec:3» : _root_.Unit) => (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$capture_avoiding_:case_1:iter:3» «typeIR?*»⟩) (fun («exec:4» : (_root_.List typeIR)) => (let «typeIR_free*» : (_root_.List typeIR) := «exec:4»; (.bind (.call ⟨(_root_.List (set _root_.String)), SpecTecCall.«$capture_avoiding_:case_1:iter:4» «typeIR_free*»⟩) (fun («exec:5» : (_root_.List (set _root_.String))) => (let «eval:6» : (_root_.List bound) := «exec:5»; (let B_capture : bound := («$unions_set» «eval:6»); (.bind (.call ⟨(_root_.List typeId), SpecTecCall.«$fresh_typeIds» (_root_.List.length «typeParameterIR*»)⟩) (fun («exec:6» : (_root_.List typeId)) => (let «eval:7» : (_root_.List typeId) := «exec:6»; (let «typeParameterIR_fresh*» : (_root_.List typeParameterIR) := «eval:7»; (.bind (.call ⟨_root_.Unit, SpecTecCall.«$capture_avoiding_:case_1:iter:8» B_capture «typeParameterIR_fresh*»⟩) (fun («exec:7» : _root_.Unit) => (.bind (.call ⟨(_root_.List typeIR), SpecTecCall.«$capture_avoiding_:case_1:iter:10» «typeParameterIR_fresh*»⟩) (fun («exec:8» : (_root_.List typeIR)) => (let «eval:11» : (_root_.List typeIR) := «exec:8»; (.bind (.call ⟨(map typeId typeIR), SpecTecCall.«$adds_map» typeId typeIR theta «typeParameterIR*» «eval:11»⟩) (fun («exec:9» : (map typeId typeIR)) => (let «eval:12» : (map typeId typeIR) := «exec:9»; (let theta_fresh : SpecTec.theta := «eval:12»; (.pure (((theta_fresh, «typeParameterIR_fresh*») : (SpecTec.theta × (_root_.List typeParameterIR)))))))))))))))))))))))))))))))))))


noncomputable def «$capture_avoiding__clauses» (input0 : theta) (input1 : (_root_.List typeParameterIR)) (input2 : bound) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$capture_avoiding_:clause:0»  input0 input1 input2)]

end SpecTec
