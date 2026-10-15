import SpecTecDecl0224

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «Lvalue_write:header-union-replace-valid-header:iter:3:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.String × value))) : (_root_.List (_root_.String × value))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Lvalue_write:header-union-replace-valid-header:iter:3:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_field : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let value_field : value := «exec:4»; (let «tail:1» : (_root_.List value) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.String × value)), SpecTecCall.«Lvalue_write:header-union-replace-valid-header:iter:3» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.String × value))) => (let «tail:2» : (_root_.List (_root_.String × value)) := «exec:5»; (.pure ((((nameIR_field, value_field) :: «tail:2») : (_root_.List (_root_.String × value)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Lvalue_write:header-union-replace-valid-header:iter:3_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Lvalue_write:header-union-replace-valid-header:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Lvalue_write:header-union-replace-valid-header:iter:3:clause:1»  input0 input1)]


noncomputable def «Copy_in_default:rule:iter:0:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List typeIR)), (([] : (_root_.List nameIR)), ([] : (_root_.List parameterInitializerOptIR)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List typeIR) × ((_root_.List nameIR) × (_root_.List parameterInitializerOptIR)))))))) | _ :: _ => .unmatch)


noncomputable def «Copy_in_default:rule:iter:0:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (match parameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let _typeIR : typeIR := «exec:5»; (let nameIR : SpecTec.nameIR := «exec:6»; (let parameterInitializerOptIR : SpecTec.parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List typeIR) × ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.parameterInitializerOptIR))))), SpecTecCall.«Copy_in_default:rule:iter:0» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List typeIR) × ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.parameterInitializerOptIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List typeIR) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List SpecTec.nameIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List SpecTec.parameterInitializerOptIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_typeIR :: «tail:3»), ((nameIR :: «tail:4»), (parameterInitializerOptIR :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List typeIR) × ((_root_.List SpecTec.nameIR) × (_root_.List SpecTec.parameterInitializerOptIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «Copy_in_default:rule:iter:0_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Copy_in_default:rule:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («Copy_in_default:rule:iter:0:clause:1»  input0)]


noncomputable def «Copy_in_default:rule:iter:1:clause:0» (input0 : (_root_.List parameterInitializerOptIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «Copy_in_default:rule:iter:1:clause:1» (input0 : (_root_.List SpecTec.parameterInitializerOptIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterInitializerOptIR : SpecTec.parameterInitializerOptIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterInitializerOptIR) := «exec:1»; (.bind (.guard (((_root_.Option.isSome parameterInitializerOptIR) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«Copy_in_default:rule:iter:1» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «Copy_in_default:rule:iter:1_clauses» (input0 : (_root_.List parameterInitializerOptIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Copy_in_default:rule:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («Copy_in_default:rule:iter:1:clause:1»  input0)]


noncomputable def «Copy_in_default:rule:iter:2:clause:0» (input0 : (_root_.List parameterInitializerOptIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List parameterInitializerIR)) : (_root_.List parameterInitializerIR)))) | _ :: _ => .unmatch)


noncomputable def «Copy_in_default:rule:iter:2:clause:1» (input0 : (_root_.List SpecTec.parameterInitializerOptIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterInitializerOptIR : SpecTec.parameterInitializerOptIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterInitializerOptIR) := «exec:1»; (match parameterInitializerOptIR with | some «exec:3» => (let parameterInitializerIR : SpecTec.parameterInitializerIR := «exec:3»; (.bind (.call ⟨(_root_.List SpecTec.parameterInitializerIR), SpecTecCall.«Copy_in_default:rule:iter:2» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.parameterInitializerIR)) => (let «tail:1» : (_root_.List SpecTec.parameterInitializerIR) := «exec:4»; (.pure (((parameterInitializerIR :: «tail:1») : (_root_.List SpecTec.parameterInitializerIR)))))))) | none => .unmatch))) | [] => .unmatch)


noncomputable def «Copy_in_default:rule:iter:2_clauses» (input0 : (_root_.List parameterInitializerOptIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Copy_in_default:rule:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («Copy_in_default:rule:iter:2:clause:1»  input0)]


noncomputable def «Copy_in_default:rule:iter:4:clause:0» (input0 : (_root_.List parameterInitializerIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List value)) : (_root_.List value)))) | _ :: _ => .unmatch)


noncomputable def «Copy_in_default:rule:iter:4:clause:1» (input0 : (_root_.List SpecTec.parameterInitializerIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterInitializerIR : SpecTec.parameterInitializerIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterInitializerIR) := «exec:1»; (match («Copy_in_default:rule:downcast:5» parameterInitializerIR) with | some «exec:3» => (let «eval:5» : constantInitializerIR := «exec:3»; (match «eval:5» with | .«'=' _VALUE %» «exec:4» => (let value : SpecTec.value := «exec:4»; (.bind (.call ⟨(_root_.List SpecTec.value), SpecTecCall.«Copy_in_default:rule:iter:4» «tail:0»⟩) (fun («exec:5» : (_root_.List SpecTec.value)) => (let «tail:1» : (_root_.List SpecTec.value) := «exec:5»; (.pure (((value :: «tail:1») : (_root_.List SpecTec.value)))))))))) | none => .unmatch))) | [] => .unmatch)


noncomputable def «Copy_in_default:rule:iter:4_clauses» (input0 : (_root_.List parameterInitializerIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Copy_in_default:rule:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Copy_in_default:rule:iter:4:clause:1»  input0)]


noncomputable def «Copy_in_default:rule:iter:6:clause:0» (input0 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List prefixedNameIR)) : (_root_.List prefixedNameIR)))) | _ :: _ => .unmatch)


noncomputable def «Copy_in_default:rule:iter:6:clause:1» (input0 : (_root_.List SpecTec.nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR : SpecTec.nameIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.nameIR) := «exec:1»; (.bind (.call ⟨(_root_.List prefixedNameIR), SpecTecCall.«Copy_in_default:rule:iter:6» «tail:0»⟩) (fun («exec:3» : (_root_.List prefixedNameIR)) => (let «tail:1» : (_root_.List prefixedNameIR) := «exec:3»; (.pure (((((prefixedNameIR._BARE nameIR) : prefixedNameIR) :: «tail:1») : (_root_.List prefixedNameIR))))))))) | [] => .unmatch)


noncomputable def «Copy_in_default:rule:iter:6_clauses» (input0 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Copy_in_default:rule:iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («Copy_in_default:rule:iter:6:clause:1»  input0)]


noncomputable def «Call_eval:definedFunctionCallee-copyin-abort:iter:2:clause:0» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Call_eval:definedFunctionCallee-copyin-abort:iter:2:clause:1» (input0 : (_root_.List SpecTec.typeArgumentIR)) (input1 : (_root_.List SpecTec.typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeParameterIR : SpecTec.typeParameterIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.typeParameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Call_eval:definedFunctionCallee-copyin-abort:iter:2» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» typeParameterIR typeArgumentIR) : (pair typeId typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Call_eval:definedFunctionCallee-copyin-abort:iter:2_clauses» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_eval:definedFunctionCallee-copyin-abort:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Call_eval:definedFunctionCallee-copyin-abort:iter:2:clause:1»  input0 input1)]


noncomputable def «Call_eval:definedFunctionCallee-cont:iter:2:clause:0» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Call_eval:definedFunctionCallee-cont:iter:2:clause:1» (input0 : (_root_.List SpecTec.typeArgumentIR)) (input1 : (_root_.List SpecTec.typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeParameterIR : SpecTec.typeParameterIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.typeParameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Call_eval:definedFunctionCallee-cont:iter:2» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» typeParameterIR typeArgumentIR) : (pair typeId typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Call_eval:definedFunctionCallee-cont:iter:2_clauses» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_eval:definedFunctionCallee-cont:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Call_eval:definedFunctionCallee-cont:iter:2:clause:1»  input0 input1)]


noncomputable def «Call_eval:externFunctionCallee-copyin-abort:iter:2:clause:0» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Call_eval:externFunctionCallee-copyin-abort:iter:2:clause:1» (input0 : (_root_.List SpecTec.typeArgumentIR)) (input1 : (_root_.List SpecTec.typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeParameterIR : SpecTec.typeParameterIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.typeParameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Call_eval:externFunctionCallee-copyin-abort:iter:2» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» typeParameterIR typeArgumentIR) : (pair typeId typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Call_eval:externFunctionCallee-copyin-abort:iter:2_clauses» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_eval:externFunctionCallee-copyin-abort:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Call_eval:externFunctionCallee-copyin-abort:iter:2:clause:1»  input0 input1)]


noncomputable def «Call_eval:externFunctionCallee-copyin-cont-call-reject:iter:2:clause:0» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String typeIR))) : (_root_.List (pair _root_.String typeIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «Call_eval:externFunctionCallee-copyin-cont-call-reject:iter:2:clause:1» (input0 : (_root_.List SpecTec.typeArgumentIR)) (input1 : (_root_.List SpecTec.typeParameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeArgumentIR : SpecTec.typeArgumentIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeArgumentIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let typeParameterIR : SpecTec.typeParameterIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.typeParameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String typeIR)), SpecTecCall.«Call_eval:externFunctionCallee-copyin-cont-call-reject:iter:2» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String typeIR))) => (let «tail:2» : (_root_.List (pair _root_.String typeIR)) := «exec:5»; (.pure (((((pair.«% ':' %» typeParameterIR typeArgumentIR) : (pair typeId typeIR)) :: «tail:2») : (_root_.List (pair _root_.String typeIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «Call_eval:externFunctionCallee-copyin-cont-call-reject:iter:2_clauses» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Call_eval:externFunctionCallee-copyin-cont-call-reject:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («Call_eval:externFunctionCallee-copyin-cont-call-reject:iter:2:clause:1»  input0 input1)]


noncomputable def «Call_eval:externFunctionCallee-copyin-cont-call-reject:iter:6:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List parameterInitializerOptIR)), (([] : (_root_.List typeIR)), ([] : (_root_.List nameIR)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR)))))))) | _ :: _ => .unmatch)


noncomputable def «Call_eval:externFunctionCallee-copyin-cont-call-reject:iter:6:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (match parameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let _typeIR : typeIR := «exec:5»; (let nameIR_param : nameIR := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR))))), SpecTecCall.«Call_eval:externFunctionCallee-copyin-cont-call-reject:iter:6» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List parameterInitializerOptIR) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List typeIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List nameIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_parameterInitializerOptIR :: «tail:3»), ((_typeIR :: «tail:4»), (nameIR_param :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR))))))))))))))))))))))) | [] => .unmatch)

end SpecTec
