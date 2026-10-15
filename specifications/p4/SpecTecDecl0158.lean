import SpecTecDecl0157

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$align_parameterListIR_given:case_4:iter:5:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String parameterIR))) : (_root_.List (pair _root_.String parameterIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$align_parameterListIR_given:case_4:iter:5:clause:1» (input0 : (_root_.List SpecTec.id)) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id : SpecTec.id := «exec:2»; (let «tail:0» : (_root_.List SpecTec.id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let parameterIR : SpecTec.parameterIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.parameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String SpecTec.parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_4:iter:5» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String SpecTec.parameterIR))) => (let «tail:2» : (_root_.List (pair _root_.String SpecTec.parameterIR)) := «exec:5»; (.pure (((((pair.«% ':' %» id parameterIR) : (pair SpecTec.id SpecTec.parameterIR)) :: «tail:2») : (_root_.List (pair _root_.String SpecTec.parameterIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$align_parameterListIR_given:case_4:iter:5_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_4:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_4:iter:5:clause:1»  input0 input1)]


noncomputable def «$align_parameterListIR_given:case_5:pattern-iter:0:clause:0» (input0 : (_root_.List (pair _root_.String parameterIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List id)), ([] : (_root_.List parameterIR))) : ((_root_.List id) × (_root_.List parameterIR))))) | _ :: _ => .unmatch)


noncomputable def «$align_parameterListIR_given:case_5:pattern-iter:0:clause:1» (input0 : (_root_.List (pair _root_.String SpecTec.parameterIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let id : SpecTec.id := «exec:3»; (let parameterIR : SpecTec.parameterIR := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair _root_.String SpecTec.parameterIR)) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.id) × (_root_.List SpecTec.parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_5:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.id) × (_root_.List SpecTec.parameterIR))) => (let «pattern-tail:1» : (_root_.List SpecTec.id) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.parameterIR) := («exec:5»).2; (.pure ((((id :: «pattern-tail:1»), (parameterIR :: «pattern-tail:2»)) : ((_root_.List SpecTec.id) × (_root_.List SpecTec.parameterIR))))))))))))) | [] => .unmatch)


noncomputable def «$align_parameterListIR_given:case_5:pattern-iter:0_clauses» (input0 : (_root_.List (pair _root_.String parameterIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_5:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_5:pattern-iter:0:clause:1»  input0)]


noncomputable def «$align_parameterListIR_given:case_5:iter:2:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String parameterIR))) : (_root_.List (pair _root_.String parameterIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$align_parameterListIR_given:case_5:iter:2:clause:1» (input0 : (_root_.List SpecTec.id)) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id : SpecTec.id := «exec:2»; (let «tail:0» : (_root_.List SpecTec.id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let parameterIR : SpecTec.parameterIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.parameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String SpecTec.parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_5:iter:2» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String SpecTec.parameterIR))) => (let «tail:2» : (_root_.List (pair _root_.String SpecTec.parameterIR)) := «exec:5»; (.pure (((((pair.«% ':' %» id parameterIR) : (pair SpecTec.id SpecTec.parameterIR)) :: «tail:2») : (_root_.List (pair _root_.String SpecTec.parameterIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$align_parameterListIR_given:case_5:iter:2_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_5:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_5:iter:2:clause:1»  input0 input1)]


noncomputable def «$align_parameterListIR_given:case_5:iter:5:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String parameterIR))) : (_root_.List (pair _root_.String parameterIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$align_parameterListIR_given:case_5:iter:5:clause:1» (input0 : (_root_.List SpecTec.id)) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id : SpecTec.id := «exec:2»; (let «tail:0» : (_root_.List SpecTec.id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let parameterIR : SpecTec.parameterIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.parameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String SpecTec.parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_5:iter:5» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String SpecTec.parameterIR))) => (let «tail:2» : (_root_.List (pair _root_.String SpecTec.parameterIR)) := «exec:5»; (.pure (((((pair.«% ':' %» id parameterIR) : (pair SpecTec.id SpecTec.parameterIR)) :: «tail:2») : (_root_.List (pair _root_.String SpecTec.parameterIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$align_parameterListIR_given:case_5:iter:5_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_5:iter:5:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_5:iter:5:clause:1»  input0 input1)]


noncomputable def «$match_overloaded_named:case_1:iter:1:clause:0» (V_T : Type) (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$match_overloaded_named:case_1:iter:1:clause:1» (V_T : Type) (input0 : (_root_.List id)) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id_param : id := «exec:2»; (let «tail:0» : (_root_.List id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let parameterIR : SpecTec.parameterIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.parameterIR) := «exec:3»; (.bind (.call ⟨id, SpecTecCall.«$id_of_parameterIR» parameterIR⟩) (fun («exec:5» : id) => (let «eval:2» : id := «exec:5»; (.bind (.guard («eval:2» = id_param)) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$match_overloaded_named:case_1:iter:1» V_T «tail:0» «tail:1»⟩) (fun («exec:6» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$match_overloaded_named:case_1:iter:1_clauses» (V_T : Type) (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_overloaded_named:case_1:iter:1:clause:0» V_T input0 input1), fun (_ : _root_.Unit) => («$match_overloaded_named:case_1:iter:1:clause:1» V_T input0 input1)]


noncomputable def «$match_overloaded_named:case_2:iter:1:clause:0» (V_T : Type) (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$match_overloaded_named:case_2:iter:1:clause:1» (V_T : Type) (input0 : (_root_.List id)) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id_param : id := «exec:2»; (let «tail:0» : (_root_.List id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let parameterIR : SpecTec.parameterIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.parameterIR) := «exec:3»; (.bind (.call ⟨id, SpecTecCall.«$id_of_parameterIR» parameterIR⟩) (fun («exec:5» : id) => (let «eval:2» : id := «exec:5»; (.bind (.guard («eval:2» = id_param)) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$match_overloaded_named:case_2:iter:1» V_T «tail:0» «tail:1»⟩) (fun («exec:6» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit)))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$match_overloaded_named:case_2:iter:1_clauses» (V_T : Type) (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_overloaded_named:case_2:iter:1:clause:0» V_T input0 input1), fun (_ : _root_.Unit) => («$match_overloaded_named:case_2:iter:1:clause:1» V_T input0 input1)]


noncomputable def «$match_overloaded_named:case_2:iter:3:clause:0» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$match_overloaded_named:case_2:iter:3:clause:1» (V_T : Type) (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_default_parameterIR» parameterIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:4» : _root_.Bool := «exec:3»; (let b_default : _root_.Bool := «eval:4»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_overloaded_named:case_2:iter:3» V_T «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((b_default :: «tail:1») : (_root_.List _root_.Bool))))))))))))) | [] => .unmatch)


noncomputable def «$match_overloaded_named:case_2:iter:3_clauses» (V_T : Type) (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_overloaded_named:case_2:iter:3:clause:0» V_T input0), fun (_ : _root_.Unit) => («$match_overloaded_named:case_2:iter:3:clause:1» V_T input0)]


noncomputable def «$match_overloaded_named:case_2:iter:7:clause:0» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$match_overloaded_named:case_2:iter:7:clause:1» (V_T : Type) (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_default_parameterIR» parameterIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:8» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_overloaded_named:case_2:iter:7» V_T «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:8» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «$match_overloaded_named:case_2:iter:7_clauses» (V_T : Type) (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_overloaded_named:case_2:iter:7:clause:0» V_T input0), fun (_ : _root_.Unit) => («$match_overloaded_named:case_2:iter:7:clause:1» V_T input0)]


noncomputable def «$match_overloaded_named:case_2:iter:11:clause:0» (V_T : Type) (input0 : (_root_.List id)) (input1 : (_root_.List id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «id_default_param*» : (_root_.List id) := input0; (match input1 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch))


noncomputable def «$match_overloaded_named:case_2:iter:11:clause:1» (V_T : Type) (input0 : (_root_.List id)) (input1 : (_root_.List id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «id_default_param*» : (_root_.List id) := input0; (match input1 with | «exec:2» :: «exec:1» => (let id_param_omitted : id := «exec:2»; (let «tail:0» : (_root_.List id) := «exec:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_overloaded_named:case_2:iter:11» V_T «id_default_param*» «tail:0»⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:3»; (.pure ((((_root_.Decidable.decide (id_param_omitted ∈ «id_default_param*»)) :: «tail:1») : (_root_.List _root_.Bool))))))))) | [] => .unmatch))


noncomputable def «$match_overloaded_named:case_2:iter:11_clauses» (V_T : Type) (input0 : (_root_.List id)) (input1 : (_root_.List id)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_overloaded_named:case_2:iter:11:clause:0» V_T input0 input1), fun (_ : _root_.Unit) => («$match_overloaded_named:case_2:iter:11:clause:1» V_T input0 input1)]


noncomputable def «$match_overloaded_named:case_2:iter:18:clause:0» (V_T : Type) (input0 : (_root_.List id)) (input1 : (_root_.List id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «id_optional_param*» : (_root_.List id) := input0; (match input1 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch))


noncomputable def «$match_overloaded_named:case_2:iter:18:clause:1» (V_T : Type) (input0 : (_root_.List id)) (input1 : (_root_.List id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «id_optional_param*» : (_root_.List id) := input0; (match input1 with | «exec:2» :: «exec:1» => (let id_param_omitted : id := «exec:2»; (let «tail:0» : (_root_.List id) := «exec:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_overloaded_named:case_2:iter:18» V_T «id_optional_param*» «tail:0»⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:3»; (.pure ((((_root_.Decidable.decide (id_param_omitted ∈ «id_optional_param*»)) :: «tail:1») : (_root_.List _root_.Bool))))))))) | [] => .unmatch))


noncomputable def «$match_overloaded_named:case_2:iter:18_clauses» (V_T : Type) (input0 : (_root_.List id)) (input1 : (_root_.List id)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$match_overloaded_named:case_2:iter:18:clause:0» V_T input0 input1), fun (_ : _root_.Unit) => («$match_overloaded_named:case_2:iter:18:clause:1» V_T input0 input1)]


noncomputable def «$match_overloaded_unnamed:case_1:iter:1:clause:0» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$match_overloaded_unnamed:case_1:iter:1:clause:1» (V_T : Type) (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_default_parameterIR» parameterIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:2» : _root_.Bool := «exec:3»; (let b_default : _root_.Bool := «eval:2»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$match_overloaded_unnamed:case_1:iter:1» V_T «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((b_default :: «tail:1») : (_root_.List _root_.Bool))))))))))))) | [] => .unmatch)

end SpecTec
