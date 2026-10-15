import SpecTecDecl0211

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$compat_table_lpm_ternary_range_key:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .BOOL  => (.bind (.guard ((0 : _root_.Nat) = («$compat_table_lpm_ternary_range_key:matches:0:row» ((typeIR.BOOL) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$compat_table_lpm_ternary_range_key:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .INT  => (.bind (.guard ((0 : _root_.Nat) = («$compat_table_lpm_ternary_range_key:matches:1:row» ((typeIR.INT) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$compat_table_lpm_ternary_range_key:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$compat_table_lpm_ternary_range_key:matches:2:row» ((typeIR.«INT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$compat_table_lpm_ternary_range_key:clause:3» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$compat_table_lpm_ternary_range_key:matches:3:row» ((typeIR.«BIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$compat_table_lpm_ternary_range_key:clause:4» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_table_lpm_ternary_range_key:matches:4:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_table_lpm_ternary_range_key» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$compat_table_lpm_ternary_range_key:clause:5» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPE «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$compat_table_lpm_ternary_range_key:matches:5:row» ((SpecTec.typeIR.TYPE _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_table_lpm_ternary_range_key» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$compat_table_lpm_ternary_range_key:clause:6» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«ENUM % `< % `> `{ % `}» «exec:1» «exec:2» «exec:3» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (let «_valueFieldIR*» : (_root_.List valueFieldIR) := «exec:3»; (.bind (.guard ((0 : _root_.Nat) = («$compat_table_lpm_ternary_range_key:matches:6:row» ((SpecTec.typeIR.«ENUM % `< % `> `{ % `}» _typeId typeIR «_valueFieldIR*») : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_table_lpm_ternary_range_key» typeIR⟩) (fun («exec:4» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:4»; (.pure ((«eval:0» : _root_.Bool))))))))))) | _ => .unmatch)


noncomputable def «$compat_table_lpm_ternary_range_key:clause:7» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$compat_table_lpm_ternary_range_key:matches:7:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$compat_table_lpm_ternary_range_key_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_table_lpm_ternary_range_key:clause:0»  input0), fun (_ : _root_.Unit) => («$compat_table_lpm_ternary_range_key:clause:1»  input0), fun (_ : _root_.Unit) => («$compat_table_lpm_ternary_range_key:clause:2»  input0), fun (_ : _root_.Unit) => («$compat_table_lpm_ternary_range_key:clause:3»  input0), fun (_ : _root_.Unit) => («$compat_table_lpm_ternary_range_key:clause:4»  input0), fun (_ : _root_.Unit) => («$compat_table_lpm_ternary_range_key:clause:5»  input0), fun (_ : _root_.Unit) => («$compat_table_lpm_ternary_range_key:clause:6»  input0), fun (_ : _root_.Unit) => («$compat_table_lpm_ternary_range_key:clause:7»  input0)]


noncomputable def «$compat_table_key:clause:0» (input0 : SpecTec.nameIR) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (let typeIR : SpecTec.typeIR := input1; (.bind (.guard ((((nameIR = "exact") ∨ (nameIR = "optional")) ∨ (nameIR = "selector")))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_table_exact_optional_key» typeIR⟩) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.bind (.guard ((«eval:0» = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))))))))


noncomputable def «$compat_table_key:clause:1» (input0 : SpecTec.nameIR) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (let typeIR : SpecTec.typeIR := input1; (.bind (.guard ((((nameIR = "lpm") ∨ (nameIR = "ternary")) ∨ (nameIR = "range")))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$compat_table_lpm_ternary_range_key» typeIR⟩) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.bind (.guard ((«eval:0» = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))))))))


noncomputable def «$compat_table_key:clause:2» (input0 : SpecTec.nameIR) (input1 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameIR : SpecTec.nameIR := input0; (let typeIR : SpecTec.typeIR := input1; (.pure ((false : _root_.Bool)))))


noncomputable def «$compat_table_key_clauses» (input0 : nameIR) (input1 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$compat_table_key:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$compat_table_key:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$compat_table_key:clause:2»  input0 input1)]


noncomputable def «$insert_NoAction_tablePropertyIR:case_2:iter:1:clause:0» (input0 : (_root_.List tableActionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List parameterListIR)), (([] : (_root_.List parameterListIR)), ([] : (_root_.List tableActionReferenceIR))))) : ((_root_.List annotationList) × ((_root_.List parameterListIR) × ((_root_.List parameterListIR) × (_root_.List tableActionReferenceIR))))))) | _ :: _ => .unmatch)


noncomputable def «$insert_NoAction_tablePropertyIR:case_2:iter:1:clause:1» (input0 : (_root_.List SpecTec.tableActionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableActionIR : SpecTec.tableActionIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableActionIR) := «exec:1»; (match tableActionIR with | .«% % '#' `( % ',' % `) ';'» «exec:3» «exec:4» «exec:5» «exec:6» => (let _annotationList : annotationList := «exec:3»; (let tableActionReferenceIR : SpecTec.tableActionReferenceIR := «exec:4»; (let _parameterListIR : parameterListIR := «exec:5»; (let _parameterListIR' : parameterListIR := «exec:6»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List parameterListIR) × ((_root_.List parameterListIR) × (_root_.List SpecTec.tableActionReferenceIR)))), SpecTecCall.«$insert_NoAction_tablePropertyIR:case_2:iter:1» «tail:0»⟩) (fun («exec:7» : ((_root_.List annotationList) × ((_root_.List parameterListIR) × ((_root_.List parameterListIR) × (_root_.List SpecTec.tableActionReferenceIR))))) => (let «tail:1» : (_root_.List annotationList) := («exec:7»).1; (let «tail:2» : (_root_.List parameterListIR) := ((«exec:7»).2).1; (let «tail:3» : (_root_.List parameterListIR) := (((«exec:7»).2).2).1; (let «tail:4» : (_root_.List SpecTec.tableActionReferenceIR) := (((«exec:7»).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_parameterListIR :: «tail:2»), ((_parameterListIR' :: «tail:3»), (tableActionReferenceIR :: «tail:4»)))) : ((_root_.List annotationList) × ((_root_.List parameterListIR) × ((_root_.List parameterListIR) × (_root_.List SpecTec.tableActionReferenceIR)))))))))))))))))))) | [] => .unmatch)


noncomputable def «$insert_NoAction_tablePropertyIR:case_2:iter:1_clauses» (input0 : (_root_.List tableActionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$insert_NoAction_tablePropertyIR:case_2:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$insert_NoAction_tablePropertyIR:case_2:iter:1:clause:1»  input0)]


noncomputable def «$insert_NoAction_tablePropertyIR:case_3:iter:1:clause:0» (input0 : (_root_.List tableActionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List parameterListIR)), (([] : (_root_.List parameterListIR)), ([] : (_root_.List tableActionReferenceIR))))) : ((_root_.List annotationList) × ((_root_.List parameterListIR) × ((_root_.List parameterListIR) × (_root_.List tableActionReferenceIR))))))) | _ :: _ => .unmatch)


noncomputable def «$insert_NoAction_tablePropertyIR:case_3:iter:1:clause:1» (input0 : (_root_.List SpecTec.tableActionIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableActionIR : SpecTec.tableActionIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableActionIR) := «exec:1»; (match tableActionIR with | .«% % '#' `( % ',' % `) ';'» «exec:3» «exec:4» «exec:5» «exec:6» => (let _annotationList : annotationList := «exec:3»; (let tableActionReferenceIR : SpecTec.tableActionReferenceIR := «exec:4»; (let _parameterListIR : parameterListIR := «exec:5»; (let _parameterListIR' : parameterListIR := «exec:6»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List parameterListIR) × ((_root_.List parameterListIR) × (_root_.List SpecTec.tableActionReferenceIR)))), SpecTecCall.«$insert_NoAction_tablePropertyIR:case_3:iter:1» «tail:0»⟩) (fun («exec:7» : ((_root_.List annotationList) × ((_root_.List parameterListIR) × ((_root_.List parameterListIR) × (_root_.List SpecTec.tableActionReferenceIR))))) => (let «tail:1» : (_root_.List annotationList) := («exec:7»).1; (let «tail:2» : (_root_.List parameterListIR) := ((«exec:7»).2).1; (let «tail:3» : (_root_.List parameterListIR) := (((«exec:7»).2).2).1; (let «tail:4» : (_root_.List SpecTec.tableActionReferenceIR) := (((«exec:7»).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_parameterListIR :: «tail:2»), ((_parameterListIR' :: «tail:3»), (tableActionReferenceIR :: «tail:4»)))) : ((_root_.List annotationList) × ((_root_.List parameterListIR) × ((_root_.List parameterListIR) × (_root_.List SpecTec.tableActionReferenceIR)))))))))))))))))))) | [] => .unmatch)


noncomputable def «$insert_NoAction_tablePropertyIR:case_3:iter:1_clauses» (input0 : (_root_.List tableActionIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$insert_NoAction_tablePropertyIR:case_3:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$insert_NoAction_tablePropertyIR:case_3:iter:1:clause:1»  input0)]


noncomputable def «$empty_strictness:case_1:iter:0:clause:0» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (pair _root_.String strict))) : (_root_.List (pair _root_.String strict))))) | _ :: _ => .unmatch)


noncomputable def «$empty_strictness:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeId : SpecTec.typeId := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeId) := «exec:1»; (.bind (.call ⟨(_root_.List (pair _root_.String strict)), SpecTecCall.«$empty_strictness:case_1:iter:0» «tail:0»⟩) (fun («exec:3» : (_root_.List (pair _root_.String strict))) => (let «tail:1» : (_root_.List (pair _root_.String strict)) := «exec:3»; (.pure (((((pair.«% ':' %» typeId ((strict.STRICT) : strict)) : (pair SpecTec.typeId strict)) :: «tail:1») : (_root_.List (pair _root_.String strict)))))))))) | [] => .unmatch)


noncomputable def «$empty_strictness:case_1:iter:0_clauses» (input0 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$empty_strictness:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$empty_strictness:case_1:iter:0:clause:1»  input0)]


noncomputable def «$empty_strictness:clause:0» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «typeId*» : (_root_.List typeId) := input0; (.bind (.call ⟨(_root_.List (pair _root_.String strict)), SpecTecCall.«$empty_strictness:case_1:iter:0» «typeId*»⟩) (fun («exec:1» : (_root_.List (pair _root_.String strict))) => (let «eval:1» : (_root_.List (pair typeId strict)) := «exec:1»; (.pure ((((set.«`{ % `}» «eval:1») : (set (pair typeId strict))) : strictness)))))))


noncomputable def «$empty_strictness_clauses» (input0 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$empty_strictness:clause:0»  input0)]


noncomputable def «$empty_constraint:case_1:iter:0:clause:0» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List (pair _root_.String infer))) : (_root_.List (pair _root_.String infer))))) | _ :: _ => .unmatch)


noncomputable def «$empty_constraint:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeId : SpecTec.typeId := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeId) := «exec:1»; (.bind (.call ⟨(_root_.List (pair _root_.String infer)), SpecTecCall.«$empty_constraint:case_1:iter:0» «tail:0»⟩) (fun («exec:3» : (_root_.List (pair _root_.String infer))) => (let «tail:1» : (_root_.List (pair _root_.String infer)) := «exec:3»; (.pure (((((pair.«% ':' %» typeId ((infer.UNKNOWN) : infer)) : (pair SpecTec.typeId infer)) :: «tail:1») : (_root_.List (pair _root_.String infer)))))))))) | [] => .unmatch)


noncomputable def «$empty_constraint:case_1:iter:0_clauses» (input0 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$empty_constraint:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$empty_constraint:case_1:iter:0:clause:1»  input0)]


noncomputable def «$empty_constraint:clause:0» (input0 : (_root_.List typeId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «typeId*» : (_root_.List typeId) := input0; (.bind (.call ⟨(_root_.List (pair _root_.String infer)), SpecTecCall.«$empty_constraint:case_1:iter:0» «typeId*»⟩) (fun («exec:1» : (_root_.List (pair _root_.String infer))) => (let «eval:1» : (_root_.List (pair typeId infer)) := «exec:1»; (.pure ((((set.«`{ % `}» «eval:1») : (set (pair typeId infer))) : constraint)))))))


noncomputable def «$empty_constraint_clauses» (input0 : (_root_.List typeId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$empty_constraint:clause:0»  input0)]


noncomputable def «$resolve_inference:case_1:pattern-iter:0:clause:0» (input0 : (_root_.List (pair _root_.String typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List typeIR)), ([] : (_root_.List typeId))) : ((_root_.List typeIR) × (_root_.List typeId))))) | _ :: _ => .unmatch)


noncomputable def «$resolve_inference:case_1:pattern-iter:0:clause:1» (input0 : (_root_.List (pair _root_.String SpecTec.typeIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let typeId : SpecTec.typeId := «exec:3»; (let typeIR : SpecTec.typeIR := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair _root_.String SpecTec.typeIR)) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.typeIR) × (_root_.List SpecTec.typeId)), SpecTecCall.«$resolve_inference:case_1:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.typeIR) × (_root_.List SpecTec.typeId))) => (let «pattern-tail:1» : (_root_.List SpecTec.typeIR) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.typeId) := («exec:5»).2; (.pure ((((typeIR :: «pattern-tail:1»), (typeId :: «pattern-tail:2»)) : ((_root_.List SpecTec.typeIR) × (_root_.List SpecTec.typeId))))))))))))) | [] => .unmatch)


noncomputable def «$resolve_inference:case_1:pattern-iter:0_clauses» (input0 : (_root_.List (pair _root_.String typeIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$resolve_inference:case_1:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$resolve_inference:case_1:pattern-iter:0:clause:1»  input0)]

end SpecTec
