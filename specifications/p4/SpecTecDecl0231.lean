import SpecTecDecl0230

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$align_tableActionArgumentInterfaces:case_1:pattern-iter:3:clause:1» (input0 : (_root_.List (pair _root_.String _root_.String))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let nameIR_alias : nameIR := «exec:3»; (let nameIR_original : nameIR := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair _root_.String _root_.String)) := «exec:1»; (.bind (.call ⟨((_root_.List nameIR) × (_root_.List nameIR)), SpecTecCall.«$align_tableActionArgumentInterfaces:case_1:pattern-iter:3» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List nameIR) × (_root_.List nameIR))) => (let «pattern-tail:1» : (_root_.List nameIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List nameIR) := («exec:5»).2; (.pure ((((nameIR_alias :: «pattern-tail:1»), (nameIR_original :: «pattern-tail:2»)) : ((_root_.List nameIR) × (_root_.List nameIR))))))))))))) | [] => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces:case_1:pattern-iter:3_clauses» (input0 : (_root_.List (pair _root_.String _root_.String))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces:case_1:pattern-iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces:case_1:pattern-iter:3:clause:1»  input0)]


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:6:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String _root_.String))) : (_root_.List (pair _root_.String _root_.String))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:6:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_alias : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_original : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String _root_.String)), SpecTecCall.«$align_tableActionArgumentInterfaces:case_1:iter:6» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String _root_.String))) => (let «tail:2» : (_root_.List (pair _root_.String _root_.String)) := «exec:5»; (.pure (((((pair.«% ':' %» nameIR_alias nameIR_original) : (pair nameIR nameIR)) :: «tail:2») : (_root_.List (pair _root_.String _root_.String)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:6_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces:case_1:iter:6:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces:case_1:iter:6:clause:1»  input0 input1)]


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:5:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «nameIR_alias*» : (_root_.List nameIR) := input0; (let «nameIR_original*» : (_root_.List nameIR) := input1; (match input2 with | [] => (.pure ((([] : (_root_.List (_root_.Option nameIR))) : (_root_.List (_root_.Option nameIR))))) | _ :: _ => .unmatch)))


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:5:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «nameIR_alias*» : (_root_.List nameIR) := input0; (let «nameIR_original*» : (_root_.List nameIR) := input1; (match input2 with | «exec:2» :: «exec:1» => (let nameIR_arg : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (.bind (.call ⟨(_root_.List (pair _root_.String _root_.String)), SpecTecCall.«$align_tableActionArgumentInterfaces:case_1:iter:6» «nameIR_alias*» «nameIR_original*»⟩) (fun («exec:3» : (_root_.List (pair _root_.String _root_.String))) => (let «eval:7» : (_root_.List (pair nameIR nameIR)) := «exec:3»; (.bind (.call ⟨(_root_.Option nameIR), SpecTecCall.«$find_map» nameIR nameIR ((set.«`{ % `}» «eval:7») : (set (pair nameIR nameIR))) nameIR_arg⟩) (fun («exec:4» : (_root_.Option nameIR)) => (let «eval:8» : (_root_.Option nameIR) := «exec:4»; (let nameIR? : (_root_.Option nameIR) := «eval:8»; (.bind (.call ⟨(_root_.List (_root_.Option nameIR)), SpecTecCall.«$align_tableActionArgumentInterfaces:case_1:iter:5» «nameIR_alias*» «nameIR_original*» «tail:0»⟩) (fun («exec:5» : (_root_.List (_root_.Option nameIR))) => (let «tail:1» : (_root_.List (_root_.Option nameIR)) := «exec:5»; (.pure (((nameIR? :: «tail:1») : (_root_.List (_root_.Option nameIR))))))))))))))))) | [] => .unmatch)))


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:5_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces:case_1:iter:5:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces:case_1:iter:5:clause:1»  input0 input1 input2)]


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:9:clause:0» (input0 : (_root_.List (_root_.Option nameIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:9:clause:1» (input0 : (_root_.List (_root_.Option nameIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR? : (_root_.Option nameIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option nameIR)) := «exec:1»; (.bind (.guard (((_root_.Option.isSome nameIR?) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$align_tableActionArgumentInterfaces:case_1:iter:9» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:9_clauses» (input0 : (_root_.List (_root_.Option nameIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces:case_1:iter:9:clause:0»  input0), fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces:case_1:iter:9:clause:1»  input0)]


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:10:clause:0» (input0 : (_root_.List (_root_.Option nameIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List nameIR)) : (_root_.List nameIR)))) | _ :: _ => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:10:clause:1» (input0 : (_root_.List (_root_.Option nameIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR? : (_root_.Option nameIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option nameIR)) := «exec:1»; (match nameIR? with | some «exec:3» => (let nameIR_arg_resolved : nameIR := «exec:3»; (.bind (.call ⟨(_root_.List nameIR), SpecTecCall.«$align_tableActionArgumentInterfaces:case_1:iter:10» «tail:0»⟩) (fun («exec:4» : (_root_.List nameIR)) => (let «tail:1» : (_root_.List nameIR) := «exec:4»; (.pure (((nameIR_arg_resolved :: «tail:1») : (_root_.List nameIR)))))))) | none => .unmatch))) | [] => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:10_clauses» (input0 : (_root_.List (_root_.Option nameIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces:case_1:iter:10:clause:0»  input0), fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces:case_1:iter:10:clause:1»  input0)]


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:11:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List parameterInitializerOptIR)), (([] : (_root_.List typeIR)), ([] : (_root_.List nameIR)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR)))))))) | _ :: _ => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:11:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (match parameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let _typeIR : typeIR := «exec:5»; (let nameIR_param : nameIR := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR))))), SpecTecCall.«$align_tableActionArgumentInterfaces:case_1:iter:11» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List parameterInitializerOptIR) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List typeIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List nameIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_parameterInitializerOptIR :: «tail:3»), ((_typeIR :: «tail:4»), (nameIR_param :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:11_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces:case_1:iter:11:clause:0»  input0), fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces:case_1:iter:11:clause:1»  input0)]


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:14:clause:0» (input0 : (_root_.List _root_.Int)) (input1 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String _root_.Int))) : (_root_.List (pair _root_.String _root_.Int))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:14:clause:1» (input0 : (_root_.List _root_.Int)) (input1 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let i_arg : _root_.Int := «exec:2»; (let «tail:0» : (_root_.List _root_.Int) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_arg_resolved : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String _root_.Int)), SpecTecCall.«$align_tableActionArgumentInterfaces:case_1:iter:14» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String _root_.Int))) => (let «tail:2» : (_root_.List (pair _root_.String _root_.Int)) := «exec:5»; (.pure (((((pair.«% ':' %» nameIR_arg_resolved i_arg) : (pair id _root_.Int)) :: «tail:2») : (_root_.List (pair _root_.String _root_.Int)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:14_clauses» (input0 : (_root_.List _root_.Int)) (input1 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces:case_1:iter:14:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces:case_1:iter:14:clause:1»  input0 input1)]


noncomputable def «$align_tableActionArgumentInterfaces':case_1:pattern-iter:0:clause:0» (input0 : (_root_.List (pair _root_.String _root_.Int))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List _root_.Int)), ([] : (_root_.List id))) : ((_root_.List _root_.Int) × (_root_.List id))))) | _ :: _ => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces':case_1:pattern-iter:0:clause:1» (input0 : (_root_.List (pair _root_.String _root_.Int))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let id_arg : id := «exec:3»; (let i_arg : _root_.Int := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair _root_.String _root_.Int)) := «exec:1»; (.bind (.call ⟨((_root_.List _root_.Int) × (_root_.List id)), SpecTecCall.«$align_tableActionArgumentInterfaces':case_1:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List _root_.Int) × (_root_.List id))) => (let «pattern-tail:1» : (_root_.List _root_.Int) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List id) := («exec:5»).2; (.pure ((((i_arg :: «pattern-tail:1»), (id_arg :: «pattern-tail:2»)) : ((_root_.List _root_.Int) × (_root_.List id))))))))))))) | [] => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces':case_1:pattern-iter:0_clauses» (input0 : (_root_.List (pair _root_.String _root_.Int))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces':case_1:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces':case_1:pattern-iter:0:clause:1»  input0)]


noncomputable def «$align_tableActionArgumentInterfaces':case_1:iter:2:clause:0» (input0 : (_root_.List _root_.Int)) (input1 : (_root_.List id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String _root_.Int))) : (_root_.List (pair _root_.String _root_.Int))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces':case_1:iter:2:clause:1» (input0 : (_root_.List _root_.Int)) (input1 : (_root_.List id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let i_arg : _root_.Int := «exec:2»; (let «tail:0» : (_root_.List _root_.Int) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let id_arg : id := «exec:4»; (let «tail:1» : (_root_.List id) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String _root_.Int)), SpecTecCall.«$align_tableActionArgumentInterfaces':case_1:iter:2» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String _root_.Int))) => (let «tail:2» : (_root_.List (pair _root_.String _root_.Int)) := «exec:5»; (.pure (((((pair.«% ':' %» id_arg i_arg) : (pair id _root_.Int)) :: «tail:2») : (_root_.List (pair _root_.String _root_.Int)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces':case_1:iter:2_clauses» (input0 : (_root_.List _root_.Int)) (input1 : (_root_.List id)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces':case_1:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces':case_1:iter:2:clause:1»  input0 input1)]


noncomputable def «$align_tableActionArgumentInterfaces':case_2:pattern-iter:0:clause:0» (input0 : (_root_.List (pair _root_.String _root_.Int))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List _root_.Int)), ([] : (_root_.List id))) : ((_root_.List _root_.Int) × (_root_.List id))))) | _ :: _ => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces':case_2:pattern-iter:0:clause:1» (input0 : (_root_.List (pair _root_.String _root_.Int))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let id_arg : id := «exec:3»; (let i_arg : _root_.Int := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair _root_.String _root_.Int)) := «exec:1»; (.bind (.call ⟨((_root_.List _root_.Int) × (_root_.List id)), SpecTecCall.«$align_tableActionArgumentInterfaces':case_2:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List _root_.Int) × (_root_.List id))) => (let «pattern-tail:1» : (_root_.List _root_.Int) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List id) := («exec:5»).2; (.pure ((((i_arg :: «pattern-tail:1»), (id_arg :: «pattern-tail:2»)) : ((_root_.List _root_.Int) × (_root_.List id))))))))))))) | [] => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces':case_2:pattern-iter:0_clauses» (input0 : (_root_.List (pair _root_.String _root_.Int))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces':case_2:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces':case_2:pattern-iter:0:clause:1»  input0)]


noncomputable def «$align_tableActionArgumentInterfaces':case_2:iter:2:clause:0» (input0 : (_root_.List _root_.Int)) (input1 : (_root_.List id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String _root_.Int))) : (_root_.List (pair _root_.String _root_.Int))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces':case_2:iter:2:clause:1» (input0 : (_root_.List _root_.Int)) (input1 : (_root_.List id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let i_arg : _root_.Int := «exec:2»; (let «tail:0» : (_root_.List _root_.Int) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let id_arg : id := «exec:4»; (let «tail:1» : (_root_.List id) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String _root_.Int)), SpecTecCall.«$align_tableActionArgumentInterfaces':case_2:iter:2» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String _root_.Int))) => (let «tail:2» : (_root_.List (pair _root_.String _root_.Int)) := «exec:5»; (.pure (((((pair.«% ':' %» id_arg i_arg) : (pair id _root_.Int)) :: «tail:2») : (_root_.List (pair _root_.String _root_.Int)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces':case_2:iter:2_clauses» (input0 : (_root_.List _root_.Int)) (input1 : (_root_.List id)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces':case_2:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces':case_2:iter:2:clause:1»  input0 input1)]

end SpecTec
