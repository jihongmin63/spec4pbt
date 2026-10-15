import SpecTecDecl0231

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$align_tableActionArgumentInterfaces':clause:0» (input0 : (map id _root_.Int)) (input1 : parameterIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «eval:1» : (_root_.List (pair id _root_.Int)) := «exec:1»; (match input1 with | .«% % % % %» «exec:2» «exec:3» «exec:4» «exec:5» «exec:6» => (let _annotationList : annotationList := «exec:2»; (let _direction : direction := «exec:3»; (let _typeIR : typeIR := «exec:4»; (let nameIR_param : nameIR := «exec:5»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:6»; (.bind (.call ⟨((_root_.List _root_.Int) × (_root_.List id)), SpecTecCall.«$align_tableActionArgumentInterfaces':case_1:pattern-iter:0» «eval:1»⟩) (fun («exec:7» : ((_root_.List _root_.Int) × (_root_.List id))) => (let «i_arg*» : (_root_.List _root_.Int) := («exec:7»).1; (let «id_arg*» : (_root_.List id) := («exec:7»).2; (.bind (.call ⟨(_root_.List (pair _root_.String _root_.Int)), SpecTecCall.«$align_tableActionArgumentInterfaces':case_1:iter:2» «i_arg*» «id_arg*»⟩) (fun («exec:8» : (_root_.List (pair _root_.String _root_.Int))) => (let «eval:3» : (_root_.List (pair id _root_.Int)) := «exec:8»; (.bind (.call ⟨(_root_.Option _root_.Int), SpecTecCall.«$find_map» id _root_.Int ((set.«`{ % `}» «eval:3») : (set (pair id _root_.Int))) nameIR_param⟩) (fun («exec:9» : (_root_.Option _root_.Int)) => (let «eval:4» : (_root_.Option _root_.Int) := «exec:9»; (let i'? : (_root_.Option _root_.Int) := «eval:4»; (.bind (.guard (((_root_.Option.isSome i'?) = true))) (fun (_ : Unit) => (match i'? with | some «exec:10» => (let i : _root_.Int := «exec:10»; (.pure ((i : _root_.Int)))) | none => .unmatch))))))))))))))))))))))


noncomputable def «$align_tableActionArgumentInterfaces':clause:1» (input0 : (map id _root_.Int)) (input1 : parameterIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«`{ % `}» «exec:1» => (let «eval:1» : (_root_.List (pair id _root_.Int)) := «exec:1»; (match input1 with | .«% % % % %» «exec:2» «exec:3» «exec:4» «exec:5» «exec:6» => (let _annotationList : annotationList := «exec:2»; (let _direction : direction := «exec:3»; (let _typeIR : typeIR := «exec:4»; (let nameIR_param : nameIR := «exec:5»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:6»; (.bind (.call ⟨((_root_.List _root_.Int) × (_root_.List id)), SpecTecCall.«$align_tableActionArgumentInterfaces':case_2:pattern-iter:0» «eval:1»⟩) (fun («exec:7» : ((_root_.List _root_.Int) × (_root_.List id))) => (let «i_arg*» : (_root_.List _root_.Int) := («exec:7»).1; (let «id_arg*» : (_root_.List id) := («exec:7»).2; (.bind (.call ⟨(_root_.List (pair _root_.String _root_.Int)), SpecTecCall.«$align_tableActionArgumentInterfaces':case_2:iter:2» «i_arg*» «id_arg*»⟩) (fun («exec:8» : (_root_.List (pair _root_.String _root_.Int))) => (let «eval:3» : (_root_.List (pair id _root_.Int)) := «exec:8»; (.bind (.call ⟨(_root_.Option _root_.Int), SpecTecCall.«$find_map» id _root_.Int ((set.«`{ % `}» «eval:3») : (set (pair id _root_.Int))) nameIR_param⟩) (fun («exec:9» : (_root_.Option _root_.Int)) => (let «eval:4» : (_root_.Option _root_.Int) := «exec:9»; (match «eval:4» with | none => (.pure (((_root_.Int.ofNat (0 : _root_.Nat)) : _root_.Int))) | some _ => .unmatch)))))))))))))))))))


noncomputable def «$align_tableActionArgumentInterfaces'_clauses» (input0 : (map id _root_.Int)) (input1 : parameterIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces':clause:1»  input0 input1)]


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:13:clause:0» (input0 : (_root_.List _root_.Int)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «i_arg*» : (_root_.List _root_.Int) := input0; (let «nameIR_arg_resolved*» : (_root_.List nameIR) := input1; (match input2 with | [] => (.pure ((([] : (_root_.List _root_.Int)) : (_root_.List _root_.Int)))) | _ :: _ => .unmatch)))


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:13:clause:1» (input0 : (_root_.List _root_.Int)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «i_arg*» : (_root_.List _root_.Int) := input0; (let «nameIR_arg_resolved*» : (_root_.List nameIR) := input1; (match input2 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨(_root_.List (pair _root_.String _root_.Int)), SpecTecCall.«$align_tableActionArgumentInterfaces:case_1:iter:14» «i_arg*» «nameIR_arg_resolved*»⟩) (fun («exec:3» : (_root_.List (pair _root_.String _root_.Int))) => (let «eval:15» : (_root_.List (pair id _root_.Int)) := «exec:3»; (.bind (.call ⟨_root_.Int, SpecTecCall.«$align_tableActionArgumentInterfaces'» ((set.«`{ % `}» «eval:15») : (set (pair id _root_.Int))) parameterIR⟩) (fun («exec:4» : _root_.Int) => (let «eval:16» : _root_.Int := «exec:4»; (let i_aligned : _root_.Int := «eval:16»; (.bind (.call ⟨(_root_.List _root_.Int), SpecTecCall.«$align_tableActionArgumentInterfaces:case_1:iter:13» «i_arg*» «nameIR_arg_resolved*» «tail:0»⟩) (fun («exec:5» : (_root_.List _root_.Int)) => (let «tail:1» : (_root_.List _root_.Int) := «exec:5»; (.pure (((i_aligned :: «tail:1») : (_root_.List _root_.Int)))))))))))))))) | [] => .unmatch)))


noncomputable def «$align_tableActionArgumentInterfaces:case_1:iter:13_clauses» (input0 : (_root_.List _root_.Int)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces:case_1:iter:13:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces:case_1:iter:13:clause:1»  input0 input1 input2)]


noncomputable def «$tableObject_create_entry_action:case_1:iter:2:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List id)), (([] : (_root_.List parameterInitializerOptIR)), ([] : (_root_.List typeIR)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))))) | _ :: _ => .unmatch)


noncomputable def «$tableObject_create_entry_action:case_1:iter:2:clause:1» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR_control : parameterIR := «exec:2»; (let «tail:0» : (_root_.List parameterIR) := «exec:1»; (match parameterIR_control with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let typeIR_param : typeIR := «exec:5»; (let _id : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR))))), SpecTecCall.«$tableObject_create_entry_action:case_1:iter:2» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List id) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List parameterInitializerOptIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List typeIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_id :: «tail:3»), ((_parameterInitializerOptIR :: «tail:4»), (typeIR_param :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «$tableObject_create_entry_action:case_1:iter:2_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$tableObject_create_entry_action:case_1:iter:2:clause:0»  input0), fun (_ : _root_.Unit) => («$tableObject_create_entry_action:case_1:iter:2:clause:1»  input0)]


noncomputable def «$tableObject_create_entry_action:case_1:iter:3:clause:0» (input0 : (_root_.List _root_.Int)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typedExpressionIR)) : (_root_.List typedExpressionIR)))) | _ :: _ => .unmatch)


noncomputable def «$tableObject_create_entry_action:case_1:iter:3:clause:1» (input0 : (_root_.List _root_.Int)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let i_arg_aligned : _root_.Int := «exec:2»; (let «tail:0» : (_root_.List _root_.Int) := «exec:1»; (let typedExpressionIR_arg : typedExpressionIR := ((typedExpressionIR.«% '#' %» ((expressionIR.D i_arg_aligned) : expressionIR) ((expressionNoteIR.«`( % % `)» ((typeIR.INT) : typeIR) ((ctk.DYN) : ctk)) : expressionNoteIR)) : typedExpressionIR); (.bind (.call ⟨(_root_.List typedExpressionIR), SpecTecCall.«$tableObject_create_entry_action:case_1:iter:3» «tail:0»⟩) (fun («exec:3» : (_root_.List typedExpressionIR)) => (let «tail:1» : (_root_.List typedExpressionIR) := «exec:3»; (.pure (((typedExpressionIR_arg :: «tail:1») : (_root_.List typedExpressionIR)))))))))) | [] => .unmatch)


noncomputable def «$tableObject_create_entry_action:case_1:iter:3_clauses» (input0 : (_root_.List _root_.Int)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$tableObject_create_entry_action:case_1:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$tableObject_create_entry_action:case_1:iter:3:clause:1»  input0)]


noncomputable def «$tableObject_create_entry_action:case_1:iter:6:clause:0» (input0 : (_root_.List (_root_.Option typedExpressionIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «$tableObject_create_entry_action:case_1:iter:6:clause:1» (input0 : (_root_.List (_root_.Option typedExpressionIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typedExpressionIR? : (_root_.Option typedExpressionIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option typedExpressionIR)) := «exec:1»; (.bind (.guard (((_root_.Option.isSome typedExpressionIR?) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$tableObject_create_entry_action:case_1:iter:6» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «$tableObject_create_entry_action:case_1:iter:6_clauses» (input0 : (_root_.List (_root_.Option typedExpressionIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$tableObject_create_entry_action:case_1:iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («$tableObject_create_entry_action:case_1:iter:6:clause:1»  input0)]


noncomputable def «$tableObject_create_entry_action:case_1:iter:7:clause:0» (input0 : (_root_.List (_root_.Option typedExpressionIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typedExpressionIR)) : (_root_.List typedExpressionIR)))) | _ :: _ => .unmatch)


noncomputable def «$tableObject_create_entry_action:case_1:iter:7:clause:1» (input0 : (_root_.List (_root_.Option typedExpressionIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typedExpressionIR? : (_root_.Option typedExpressionIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option typedExpressionIR)) := «exec:1»; (match typedExpressionIR? with | some «exec:3» => (let typedExpressionIR_arg_cast : typedExpressionIR := «exec:3»; (.bind (.call ⟨(_root_.List typedExpressionIR), SpecTecCall.«$tableObject_create_entry_action:case_1:iter:7» «tail:0»⟩) (fun («exec:4» : (_root_.List typedExpressionIR)) => (let «tail:1» : (_root_.List typedExpressionIR) := «exec:4»; (.pure (((typedExpressionIR_arg_cast :: «tail:1») : (_root_.List typedExpressionIR)))))))) | none => .unmatch))) | [] => .unmatch)


noncomputable def «$tableObject_create_entry_action:case_1:iter:7_clauses» (input0 : (_root_.List (_root_.Option typedExpressionIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$tableObject_create_entry_action:case_1:iter:7:clause:0»  input0), fun (_ : _root_.Unit) => («$tableObject_create_entry_action:case_1:iter:7:clause:1»  input0)]


noncomputable def «$tableObject_create_entry_action:case_2:iter:3:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List id)), (([] : (_root_.List parameterInitializerOptIR)), ([] : (_root_.List typeIR)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))))) | _ :: _ => .unmatch)


noncomputable def «$tableObject_create_entry_action:case_2:iter:3:clause:1» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR_control : parameterIR := «exec:2»; (let «tail:0» : (_root_.List parameterIR) := «exec:1»; (match parameterIR_control with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let typeIR_param : typeIR := «exec:5»; (let _id : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR))))), SpecTecCall.«$tableObject_create_entry_action:case_2:iter:3» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List id) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List parameterInitializerOptIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List typeIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_id :: «tail:3»), ((_parameterInitializerOptIR :: «tail:4»), (typeIR_param :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «$tableObject_create_entry_action:case_2:iter:3_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$tableObject_create_entry_action:case_2:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$tableObject_create_entry_action:case_2:iter:3:clause:1»  input0)]


noncomputable def «$tableObject_create_entry_action:case_2:iter:4:clause:0» (input0 : (_root_.List _root_.Int)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typedExpressionIR)) : (_root_.List typedExpressionIR)))) | _ :: _ => .unmatch)


noncomputable def «$tableObject_create_entry_action:case_2:iter:4:clause:1» (input0 : (_root_.List _root_.Int)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let i_arg_aligned : _root_.Int := «exec:2»; (let «tail:0» : (_root_.List _root_.Int) := «exec:1»; (let typedExpressionIR_arg : typedExpressionIR := ((typedExpressionIR.«% '#' %» ((expressionIR.D i_arg_aligned) : expressionIR) ((expressionNoteIR.«`( % % `)» ((typeIR.INT) : typeIR) ((ctk.DYN) : ctk)) : expressionNoteIR)) : typedExpressionIR); (.bind (.call ⟨(_root_.List typedExpressionIR), SpecTecCall.«$tableObject_create_entry_action:case_2:iter:4» «tail:0»⟩) (fun («exec:3» : (_root_.List typedExpressionIR)) => (let «tail:1» : (_root_.List typedExpressionIR) := «exec:3»; (.pure (((typedExpressionIR_arg :: «tail:1») : (_root_.List typedExpressionIR)))))))))) | [] => .unmatch)


noncomputable def «$tableObject_create_entry_action:case_2:iter:4_clauses» (input0 : (_root_.List _root_.Int)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$tableObject_create_entry_action:case_2:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («$tableObject_create_entry_action:case_2:iter:4:clause:1»  input0)]


noncomputable def «$tableObject_create_entry_action:case_2:iter:7:clause:0» (input0 : (_root_.List (_root_.Option typedExpressionIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «$tableObject_create_entry_action:case_2:iter:7:clause:1» (input0 : (_root_.List (_root_.Option typedExpressionIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typedExpressionIR? : (_root_.Option typedExpressionIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option typedExpressionIR)) := «exec:1»; (.bind (.guard (((_root_.Option.isSome typedExpressionIR?) = true))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$tableObject_create_entry_action:case_2:iter:7» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «$tableObject_create_entry_action:case_2:iter:7_clauses» (input0 : (_root_.List (_root_.Option typedExpressionIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$tableObject_create_entry_action:case_2:iter:7:clause:0»  input0), fun (_ : _root_.Unit) => («$tableObject_create_entry_action:case_2:iter:7:clause:1»  input0)]


noncomputable def «$tableObject_create_entry_action:case_2:iter:8:clause:0» (input0 : (_root_.List (_root_.Option typedExpressionIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List typedExpressionIR)) : (_root_.List typedExpressionIR)))) | _ :: _ => .unmatch)


noncomputable def «$tableObject_create_entry_action:case_2:iter:8:clause:1» (input0 : (_root_.List (_root_.Option typedExpressionIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typedExpressionIR? : (_root_.Option typedExpressionIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.Option typedExpressionIR)) := «exec:1»; (match typedExpressionIR? with | some «exec:3» => (let typedExpressionIR_arg_cast : typedExpressionIR := «exec:3»; (.bind (.call ⟨(_root_.List typedExpressionIR), SpecTecCall.«$tableObject_create_entry_action:case_2:iter:8» «tail:0»⟩) (fun («exec:4» : (_root_.List typedExpressionIR)) => (let «tail:1» : (_root_.List typedExpressionIR) := «exec:4»; (.pure (((typedExpressionIR_arg_cast :: «tail:1») : (_root_.List typedExpressionIR)))))))) | none => .unmatch))) | [] => .unmatch)


noncomputable def «$tableObject_create_entry_action:case_2:iter:8_clauses» (input0 : (_root_.List (_root_.Option typedExpressionIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$tableObject_create_entry_action:case_2:iter:8:clause:0»  input0), fun (_ : _root_.Unit) => («$tableObject_create_entry_action:case_2:iter:8:clause:1»  input0)]


noncomputable def «$V1Model_meta_fields_of_index:case_1:pattern-iter:4:clause:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List typeIR)), ([] : (_root_.List nameIR)))) : ((_root_.List annotationList) × ((_root_.List typeIR) × (_root_.List nameIR)))))) | _ :: _ => .unmatch)


noncomputable def «$V1Model_meta_fields_of_index:case_1:pattern-iter:4:clause:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% % % ';'» «exec:3» «exec:4» «exec:5» => (let _annotationList : annotationList := «exec:3»; (let _typeIR : typeIR := «exec:4»; (let nameIR : SpecTec.nameIR := «exec:5»; (let «pattern-tail:0» : (_root_.List fieldTypeIR) := «exec:1»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List typeIR) × (_root_.List SpecTec.nameIR))), SpecTecCall.«$V1Model_meta_fields_of_index:case_1:pattern-iter:4» «pattern-tail:0»⟩) (fun («exec:6» : ((_root_.List annotationList) × ((_root_.List typeIR) × (_root_.List SpecTec.nameIR)))) => (let «pattern-tail:1» : (_root_.List annotationList) := («exec:6»).1; (let «pattern-tail:2» : (_root_.List typeIR) := ((«exec:6»).2).1; (let «pattern-tail:3» : (_root_.List SpecTec.nameIR) := ((«exec:6»).2).2; (.pure ((((_annotationList :: «pattern-tail:1»), ((_typeIR :: «pattern-tail:2»), (nameIR :: «pattern-tail:3»))) : ((_root_.List annotationList) × ((_root_.List typeIR) × (_root_.List SpecTec.nameIR)))))))))))))))) | [] => .unmatch)

end SpecTec
