import SpecTecDecl0229

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$alias_to_original_lookup_map:case_1:iter:7_clauses» (input0 : (_root_.List (_root_.Option nameIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:7:clause:0»  input0), fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:7:clause:1»  input0)]


noncomputable def «$alias_to_original_lookup_map:case_1:iter:6:clause:0» (input0 : (_root_.List (_root_.List (_root_.Option nameIR)))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List (_root_.List nameIR)))) : (_root_.List (_root_.List (_root_.List nameIR)))))) | _ :: _ => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:6:clause:1» (input0 : (_root_.List (_root_.List (_root_.Option nameIR)))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let «nameIR_names_opt?*» : (_root_.List (_root_.Option nameIR)) := «exec:2»; (let «tail:0» : (_root_.List (_root_.List (_root_.Option nameIR))) := «exec:1»; (.bind (.call ⟨(_root_.List (_root_.List nameIR)), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:7» «nameIR_names_opt?*»⟩) (fun («exec:3» : (_root_.List (_root_.List nameIR))) => (let «nameIR_names_seq**» : (_root_.List (_root_.List nameIR)) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.List (_root_.List nameIR))), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:6» «tail:0»⟩) (fun («exec:4» : (_root_.List (_root_.List (_root_.List nameIR)))) => (let «tail:1» : (_root_.List (_root_.List (_root_.List nameIR))) := «exec:4»; (.pure (((«nameIR_names_seq**» :: «tail:1») : (_root_.List (_root_.List (_root_.List nameIR)))))))))))))) | [] => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:6_clauses» (input0 : (_root_.List (_root_.List (_root_.Option nameIR)))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:6:clause:1»  input0)]


noncomputable def «$alias_to_original_lookup_map:case_1:iter:9:clause:0» (input0 : (_root_.List (_root_.List (_root_.List nameIR)))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (_root_.List nameIR))) : (_root_.List (_root_.List nameIR))))) | _ :: _ => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:9:clause:1» (input0 : (_root_.List (_root_.List (_root_.List nameIR)))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let «nameIR_names_seq**» : (_root_.List (_root_.List nameIR)) := «exec:2»; (let «tail:0» : (_root_.List (_root_.List (_root_.List nameIR))) := «exec:1»; (let «nameIR_names*» : (_root_.List nameIR) := («$concat_» (X := nameIR) «nameIR_names_seq**»); (.bind (.call ⟨(_root_.List (_root_.List nameIR)), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:9» «tail:0»⟩) (fun («exec:3» : (_root_.List (_root_.List nameIR))) => (let «tail:1» : (_root_.List (_root_.List nameIR)) := «exec:3»; (.pure (((«nameIR_names*» :: «tail:1») : (_root_.List (_root_.List nameIR))))))))))) | [] => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:9_clauses» (input0 : (_root_.List (_root_.List (_root_.List nameIR)))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:9:clause:0»  input0), fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:9:clause:1»  input0)]


noncomputable def «$alias_to_original_lookup_map:case_1:iter:10:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List (_root_.List nameIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (_root_.String × (_root_.List _root_.String)))) : (_root_.List (_root_.String × (_root_.List _root_.String)))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:10:clause:1» (input0 : (_root_.List SpecTec.id)) (input1 : (_root_.List (_root_.List nameIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id : SpecTec.id := «exec:2»; (let «tail:0» : (_root_.List SpecTec.id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let «nameIR_names*» : (_root_.List nameIR) := «exec:4»; (let «tail:1» : (_root_.List (_root_.List nameIR)) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.String × (_root_.List _root_.String))), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:10» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (_root_.String × (_root_.List _root_.String)))) => (let «tail:2» : (_root_.List (_root_.String × (_root_.List _root_.String))) := «exec:5»; (.pure ((((id, «nameIR_names*») :: «tail:2») : (_root_.List (_root_.String × (_root_.List _root_.String))))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:10_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List (_root_.List nameIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:10:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:10:clause:1»  input0 input1)]


noncomputable def «$alias_to_original_lookup_map:case_1:iter:12:clause:0» (input0 : (_root_.List (_root_.List nameIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:12:clause:1» (input0 : (_root_.List (_root_.List nameIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let «nameIR_names*» : (_root_.List nameIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.List nameIR)) := «exec:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:12» «tail:0»⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:3»; (.pure ((((_root_.Decidable.decide ((_root_.List.length «nameIR_names*») > (0 : _root_.Nat))) :: «tail:1») : (_root_.List _root_.Bool))))))))) | [] => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:12_clauses» (input0 : (_root_.List (_root_.List nameIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:12:clause:0»  input0), fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:12:clause:1»  input0)]


noncomputable def «$alias_to_original_lookup_map:case_1:pattern-iter:15:clause:0» (input0 : (_root_.List (_root_.String × (_root_.List _root_.String)))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List (_root_.List nameIR))), ([] : (_root_.List nameIR))) : ((_root_.List (_root_.List nameIR)) × (_root_.List nameIR))))) | _ :: _ => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:pattern-iter:15:clause:1» (input0 : (_root_.List (_root_.String × (_root_.List _root_.String)))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_original : nameIR := («exec:2»).1; (let «nameIR_aliases*» : (_root_.List nameIR) := («exec:2»).2; (let «pattern-tail:0» : (_root_.List (_root_.String × (_root_.List _root_.String))) := «exec:1»; (.bind (.call ⟨((_root_.List (_root_.List nameIR)) × (_root_.List nameIR)), SpecTecCall.«$alias_to_original_lookup_map:case_1:pattern-iter:15» «pattern-tail:0»⟩) (fun («exec:3» : ((_root_.List (_root_.List nameIR)) × (_root_.List nameIR))) => (let «pattern-tail:1» : (_root_.List (_root_.List nameIR)) := («exec:3»).1; (let «pattern-tail:2» : (_root_.List nameIR) := («exec:3»).2; (.pure ((((«nameIR_aliases*» :: «pattern-tail:1»), (nameIR_original :: «pattern-tail:2»)) : ((_root_.List (_root_.List nameIR)) × (_root_.List nameIR)))))))))))) | [] => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:pattern-iter:15_clauses» (input0 : (_root_.List (_root_.String × (_root_.List _root_.String)))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:pattern-iter:15:clause:0»  input0), fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:pattern-iter:15:clause:1»  input0)]


noncomputable def «$alias_to_original_lookup_map:case_1:iter:17:clause:0» (input0 : (_root_.List (_root_.List nameIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((_root_.Unit.unit) : _root_.Unit))) | _ :: _ => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:17:clause:1» (input0 : (_root_.List (_root_.List nameIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let «nameIR_aliases*» : (_root_.List nameIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.List nameIR)) := «exec:1»; (.bind (.guard (((0 : _root_.Nat) < (_root_.List.length «nameIR_aliases*»)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Unit, SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:17» «tail:0»⟩) (fun («exec:3» : _root_.Unit) => (.pure (((_root_.Unit.unit) : _root_.Unit))))))))) | [] => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:17_clauses» (input0 : (_root_.List (_root_.List nameIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:17:clause:0»  input0), fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:17:clause:1»  input0)]


noncomputable def «$alias_to_original_lookup_map:case_1:iter:18:clause:0» (input0 : (_root_.List (_root_.List nameIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.String)) : (_root_.List _root_.String)))) | _ :: _ => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:18:clause:1» (input0 : (_root_.List (_root_.List nameIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let «nameIR_aliases*» : (_root_.List nameIR) := «exec:2»; (let «tail:0» : (_root_.List (_root_.List nameIR)) := «exec:1»; (match («nameIR_aliases*»[(0 : _root_.Nat)]?) with | some «exec:3» => (let «eval:19» : nameIR := «exec:3»; (.bind (.call ⟨(_root_.List _root_.String), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:18» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.String)) => (let «tail:1» : (_root_.List _root_.String) := «exec:4»; (.pure (((«eval:19» :: «tail:1») : (_root_.List _root_.String)))))))) | none => .unmatch))) | [] => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:18_clauses» (input0 : (_root_.List (_root_.List nameIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:18:clause:0»  input0), fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:18:clause:1»  input0)]


noncomputable def «$alias_to_original_lookup_map:case_1:iter:21:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String _root_.String))) : (_root_.List (pair _root_.String _root_.String))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:21:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_alias : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let nameIR_original : nameIR := «exec:4»; (let «tail:1» : (_root_.List nameIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String _root_.String)), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:21» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String _root_.String))) => (let «tail:2» : (_root_.List (pair _root_.String _root_.String)) := «exec:5»; (.pure (((((pair.«% ':' %» nameIR_alias nameIR_original) : (pair nameIR nameIR)) :: «tail:2») : (_root_.List (pair _root_.String _root_.String)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:21_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:21:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:21:clause:1»  input0 input1)]


noncomputable def «$alias_to_original_lookup_map:case_1:iter:23:clause:0» (input0 : (_root_.List id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (pair _root_.String _root_.String))) : (_root_.List (pair _root_.String _root_.String))))) | _ :: _ => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:23:clause:1» (input0 : (_root_.List SpecTec.id)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id : SpecTec.id := «exec:2»; (let «tail:0» : (_root_.List SpecTec.id) := «exec:1»; (.bind (.call ⟨(_root_.List (pair _root_.String _root_.String)), SpecTecCall.«$alias_to_original_lookup_map:case_1:iter:23» «tail:0»⟩) (fun («exec:3» : (_root_.List (pair _root_.String _root_.String))) => (let «tail:1» : (_root_.List (pair _root_.String _root_.String)) := «exec:3»; (.pure (((((pair.«% ':' %» id id) : (pair nameIR nameIR)) :: «tail:1») : (_root_.List (pair _root_.String _root_.String)))))))))) | [] => .unmatch)


noncomputable def «$alias_to_original_lookup_map:case_1:iter:23_clauses» (input0 : (_root_.List id)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:23:clause:0»  input0), fun (_ : _root_.Unit) => («$alias_to_original_lookup_map:case_1:iter:23:clause:1»  input0)]


noncomputable def «$align_tableActionArgumentInterfaces:case_1:pattern-iter:0:clause:0» (input0 : (_root_.List (_root_.String × _root_.Int))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List _root_.Int)), ([] : (_root_.List nameIR))) : ((_root_.List _root_.Int) × (_root_.List nameIR))))) | _ :: _ => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces:case_1:pattern-iter:0:clause:1» (input0 : (_root_.List (_root_.String × _root_.Int))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_arg : nameIR := («exec:2»).1; (let i_arg : _root_.Int := («exec:2»).2; (let «pattern-tail:0» : (_root_.List (_root_.String × _root_.Int)) := «exec:1»; (.bind (.call ⟨((_root_.List _root_.Int) × (_root_.List nameIR)), SpecTecCall.«$align_tableActionArgumentInterfaces:case_1:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:3» : ((_root_.List _root_.Int) × (_root_.List nameIR))) => (let «pattern-tail:1» : (_root_.List _root_.Int) := («exec:3»).1; (let «pattern-tail:2» : (_root_.List nameIR) := («exec:3»).2; (.pure ((((i_arg :: «pattern-tail:1»), (nameIR_arg :: «pattern-tail:2»)) : ((_root_.List _root_.Int) × (_root_.List nameIR)))))))))))) | [] => .unmatch)


noncomputable def «$align_tableActionArgumentInterfaces:case_1:pattern-iter:0_clauses» (input0 : (_root_.List (_root_.String × _root_.Int))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces:case_1:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$align_tableActionArgumentInterfaces:case_1:pattern-iter:0:clause:1»  input0)]


noncomputable def «$align_tableActionArgumentInterfaces:case_1:pattern-iter:3:clause:0» (input0 : (_root_.List (pair _root_.String _root_.String))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List nameIR)), ([] : (_root_.List nameIR))) : ((_root_.List nameIR) × (_root_.List nameIR))))) | _ :: _ => .unmatch)

end SpecTec
