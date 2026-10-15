import SpecTecDecl0156

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$partition_parameterListIR:clause:0» (input0 : (_root_.List parameterIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «parameterIR*» : (_root_.List parameterIR) := input0; (let «_nameIR*» : (_root_.List nameIR) := input1; (let «_nameIR'*» : (_root_.List nameIR) := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «parameterIR*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure (((([] : (_root_.List parameterIR)), (([] : (_root_.List parameterIR)), ([] : (_root_.List parameterIR)))) : ((_root_.List parameterIR) × ((_root_.List parameterIR) × (_root_.List parameterIR)))))))))))


noncomputable def «$partition_parameterListIR:clause:1» (input0 : (_root_.List parameterIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «parameterIR*» : (_root_.List parameterIR) := input0; (let «nameIR_default*» : (_root_.List nameIR) := input1; (let «nameIR_optional*» : (_root_.List nameIR) := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «parameterIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «parameterIR*» with | «exec:2» :: «exec:1» => (let parameterIR_h : parameterIR := «exec:2»; (let «parameterIR_t*» : (_root_.List parameterIR) := «exec:1»; (.bind (.call ⟨((_root_.List parameterIR) × ((_root_.List parameterIR) × (_root_.List parameterIR))), SpecTecCall.«$partition_parameterListIR» «parameterIR_t*» «nameIR_default*» «nameIR_optional*»⟩) (fun («exec:3» : ((_root_.List parameterIR) × ((_root_.List parameterIR) × (_root_.List parameterIR)))) => (let «eval:0» : ((_root_.List parameterIR) × ((_root_.List parameterIR) × (_root_.List parameterIR))) := «exec:3»; (let «parameterIR_given*» : (_root_.List parameterIR) := («eval:0»).1; (let «parameterIR_default*» : (_root_.List parameterIR) := ((«eval:0»).2).1; (let «parameterIR_optional*» : (_root_.List parameterIR) := ((«eval:0»).2).2; (match parameterIR_h with | .«% % % % %» «exec:4» «exec:5» «exec:6» «exec:7» «exec:8» => (let _annotationList : annotationList := «exec:4»; (let _direction : direction := «exec:5»; (let _typeIR : typeIR := «exec:6»; (let nameIR_h : nameIR := «exec:7»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:8»; (.bind (.guard ((nameIR_h ∈ «nameIR_default*»))) (fun (_ : Unit) => (.pure (((«parameterIR_given*», ((parameterIR_h :: «parameterIR_default*»), «parameterIR_optional*»)) : ((_root_.List parameterIR) × ((_root_.List parameterIR) × (_root_.List parameterIR)))))))))))))))))))))) | [] => .unmatch))))))


noncomputable def «$partition_parameterListIR:clause:2» (input0 : (_root_.List parameterIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «parameterIR*» : (_root_.List parameterIR) := input0; (let «nameIR_default*» : (_root_.List nameIR) := input1; (let «nameIR_optional*» : (_root_.List nameIR) := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «parameterIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «parameterIR*» with | «exec:2» :: «exec:1» => (let parameterIR_h : parameterIR := «exec:2»; (let «parameterIR_t*» : (_root_.List parameterIR) := «exec:1»; (.bind (.call ⟨((_root_.List parameterIR) × ((_root_.List parameterIR) × (_root_.List parameterIR))), SpecTecCall.«$partition_parameterListIR» «parameterIR_t*» «nameIR_default*» «nameIR_optional*»⟩) (fun («exec:3» : ((_root_.List parameterIR) × ((_root_.List parameterIR) × (_root_.List parameterIR)))) => (let «eval:0» : ((_root_.List parameterIR) × ((_root_.List parameterIR) × (_root_.List parameterIR))) := «exec:3»; (let «parameterIR_given*» : (_root_.List parameterIR) := («eval:0»).1; (let «parameterIR_default*» : (_root_.List parameterIR) := ((«eval:0»).2).1; (let «parameterIR_optional*» : (_root_.List parameterIR) := ((«eval:0»).2).2; (match parameterIR_h with | .«% % % % %» «exec:4» «exec:5» «exec:6» «exec:7» «exec:8» => (let _annotationList : annotationList := «exec:4»; (let _direction : direction := «exec:5»; (let _typeIR : typeIR := «exec:6»; (let nameIR_h : nameIR := «exec:7»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:8»; (.bind (.guard ((nameIR_h ∈ «nameIR_optional*»))) (fun (_ : Unit) => (.pure (((«parameterIR_given*», («parameterIR_default*», (parameterIR_h :: «parameterIR_optional*»))) : ((_root_.List parameterIR) × ((_root_.List parameterIR) × (_root_.List parameterIR)))))))))))))))))))))) | [] => .unmatch))))))


noncomputable def «$partition_parameterListIR:clause:3» (input0 : (_root_.List parameterIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List nameIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «parameterIR*» : (_root_.List parameterIR) := input0; (let «nameIR_default*» : (_root_.List nameIR) := input1; (let «nameIR_optional*» : (_root_.List nameIR) := input2; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «parameterIR*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «parameterIR*» with | «exec:2» :: «exec:1» => (let parameterIR_h : parameterIR := «exec:2»; (let «parameterIR_t*» : (_root_.List parameterIR) := «exec:1»; (.bind (.call ⟨((_root_.List parameterIR) × ((_root_.List parameterIR) × (_root_.List parameterIR))), SpecTecCall.«$partition_parameterListIR» «parameterIR_t*» «nameIR_default*» «nameIR_optional*»⟩) (fun («exec:3» : ((_root_.List parameterIR) × ((_root_.List parameterIR) × (_root_.List parameterIR)))) => (let «eval:0» : ((_root_.List parameterIR) × ((_root_.List parameterIR) × (_root_.List parameterIR))) := «exec:3»; (let «parameterIR_given*» : (_root_.List parameterIR) := («eval:0»).1; (let «parameterIR_default*» : (_root_.List parameterIR) := ((«eval:0»).2).1; (let «parameterIR_optional*» : (_root_.List parameterIR) := ((«eval:0»).2).2; (match parameterIR_h with | .«% % % % %» «exec:4» «exec:5» «exec:6» «exec:7» «exec:8» => (let _annotationList : annotationList := «exec:4»; (let _direction : direction := «exec:5»; (let _typeIR : typeIR := «exec:6»; (let nameIR_h : nameIR := «exec:7»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:8»; (.bind (.guard ((¬ (nameIR_h ∈ «nameIR_default*»)))) (fun (_ : Unit) => (.bind (.guard ((¬ (nameIR_h ∈ «nameIR_optional*»)))) (fun (_ : Unit) => (.pure ((((parameterIR_h :: «parameterIR_given*»), («parameterIR_default*», «parameterIR_optional*»)) : ((_root_.List parameterIR) × ((_root_.List parameterIR) × (_root_.List parameterIR)))))))))))))))))))))))) | [] => .unmatch))))))


noncomputable def «$partition_parameterListIR_clauses» (input0 : (_root_.List parameterIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List nameIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$partition_parameterListIR:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$partition_parameterListIR:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$partition_parameterListIR:clause:2»  input0 input1 input2), fun (_ : _root_.Unit) => («$partition_parameterListIR:clause:3»  input0 input1 input2)]


noncomputable def «$align_parameterListIR:case_1:iter:1:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List parameterInitializerOptIR)), (([] : (_root_.List typeIR)), ([] : (_root_.List nameIR)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR)))))))) | _ :: _ => .unmatch)


noncomputable def «$align_parameterListIR:case_1:iter:1:clause:1» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR_given : parameterIR := «exec:2»; (let «tail:0» : (_root_.List parameterIR) := «exec:1»; (match parameterIR_given with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let _typeIR : typeIR := «exec:5»; (let nameIR_given : nameIR := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR))))), SpecTecCall.«$align_parameterListIR:case_1:iter:1» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List parameterInitializerOptIR) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List typeIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List nameIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_parameterInitializerOptIR :: «tail:3»), ((_typeIR :: «tail:4»), (nameIR_given :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «$align_parameterListIR:case_1:iter:1_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_parameterListIR:case_1:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$align_parameterListIR:case_1:iter:1:clause:1»  input0)]


noncomputable def «$align_parameterListIR:case_1:iter:2:clause:0» (input0 : (_root_.List nameIR)) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String parameterIR))) : (_root_.List (pair _root_.String parameterIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$align_parameterListIR:case_1:iter:2:clause:1» (input0 : (_root_.List nameIR)) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let nameIR_given : nameIR := «exec:2»; (let «tail:0» : (_root_.List nameIR) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let parameterIR_given : parameterIR := «exec:4»; (let «tail:1» : (_root_.List parameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String parameterIR)), SpecTecCall.«$align_parameterListIR:case_1:iter:2» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String parameterIR))) => (let «tail:2» : (_root_.List (pair _root_.String parameterIR)) := «exec:5»; (.pure (((((pair.«% ':' %» nameIR_given parameterIR_given) : (pair id parameterIR)) :: «tail:2») : (_root_.List (pair _root_.String parameterIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$align_parameterListIR:case_1:iter:2_clauses» (input0 : (_root_.List nameIR)) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_parameterListIR:case_1:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$align_parameterListIR:case_1:iter:2:clause:1»  input0 input1)]


noncomputable def «$align_parameterListIR_given:case_1:pattern-iter:0:clause:0» (input0 : (_root_.List (pair _root_.String parameterIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List id)), ([] : (_root_.List parameterIR))) : ((_root_.List id) × (_root_.List parameterIR))))) | _ :: _ => .unmatch)


noncomputable def «$align_parameterListIR_given:case_1:pattern-iter:0:clause:1» (input0 : (_root_.List (pair _root_.String SpecTec.parameterIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let id : SpecTec.id := «exec:3»; (let parameterIR : SpecTec.parameterIR := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair _root_.String SpecTec.parameterIR)) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.id) × (_root_.List SpecTec.parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_1:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.id) × (_root_.List SpecTec.parameterIR))) => (let «pattern-tail:1» : (_root_.List SpecTec.id) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.parameterIR) := («exec:5»).2; (.pure ((((id :: «pattern-tail:1»), (parameterIR :: «pattern-tail:2»)) : ((_root_.List SpecTec.id) × (_root_.List SpecTec.parameterIR))))))))))))) | [] => .unmatch)


noncomputable def «$align_parameterListIR_given:case_1:pattern-iter:0_clauses» (input0 : (_root_.List (pair _root_.String parameterIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_1:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_1:pattern-iter:0:clause:1»  input0)]


noncomputable def «$align_parameterListIR_given:case_2:pattern-iter:0:clause:0» (input0 : (_root_.List (pair _root_.String parameterIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List id)), ([] : (_root_.List parameterIR))) : ((_root_.List id) × (_root_.List parameterIR))))) | _ :: _ => .unmatch)


noncomputable def «$align_parameterListIR_given:case_2:pattern-iter:0:clause:1» (input0 : (_root_.List (pair _root_.String SpecTec.parameterIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let id : SpecTec.id := «exec:3»; (let parameterIR : SpecTec.parameterIR := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair _root_.String SpecTec.parameterIR)) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.id) × (_root_.List SpecTec.parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_2:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.id) × (_root_.List SpecTec.parameterIR))) => (let «pattern-tail:1» : (_root_.List SpecTec.id) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.parameterIR) := («exec:5»).2; (.pure ((((id :: «pattern-tail:1»), (parameterIR :: «pattern-tail:2»)) : ((_root_.List SpecTec.id) × (_root_.List SpecTec.parameterIR))))))))))))) | [] => .unmatch)


noncomputable def «$align_parameterListIR_given:case_2:pattern-iter:0_clauses» (input0 : (_root_.List (pair _root_.String parameterIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_2:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_2:pattern-iter:0:clause:1»  input0)]


noncomputable def «$align_parameterListIR_given:case_2:iter:3:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String parameterIR))) : (_root_.List (pair _root_.String parameterIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$align_parameterListIR_given:case_2:iter:3:clause:1» (input0 : (_root_.List SpecTec.id)) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id : SpecTec.id := «exec:2»; (let «tail:0» : (_root_.List SpecTec.id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let parameterIR : SpecTec.parameterIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.parameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String SpecTec.parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_2:iter:3» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String SpecTec.parameterIR))) => (let «tail:2» : (_root_.List (pair _root_.String SpecTec.parameterIR)) := «exec:5»; (.pure (((((pair.«% ':' %» id parameterIR) : (pair SpecTec.id SpecTec.parameterIR)) :: «tail:2») : (_root_.List (pair _root_.String SpecTec.parameterIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$align_parameterListIR_given:case_2:iter:3_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_2:iter:3:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_2:iter:3:clause:1»  input0 input1)]


noncomputable def «$align_parameterListIR_given:case_3:pattern-iter:0:clause:0» (input0 : (_root_.List (pair _root_.String parameterIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List id)), ([] : (_root_.List parameterIR))) : ((_root_.List id) × (_root_.List parameterIR))))) | _ :: _ => .unmatch)


noncomputable def «$align_parameterListIR_given:case_3:pattern-iter:0:clause:1» (input0 : (_root_.List (pair _root_.String SpecTec.parameterIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let id : SpecTec.id := «exec:3»; (let parameterIR : SpecTec.parameterIR := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair _root_.String SpecTec.parameterIR)) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.id) × (_root_.List SpecTec.parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_3:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.id) × (_root_.List SpecTec.parameterIR))) => (let «pattern-tail:1» : (_root_.List SpecTec.id) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.parameterIR) := («exec:5»).2; (.pure ((((id :: «pattern-tail:1»), (parameterIR :: «pattern-tail:2»)) : ((_root_.List SpecTec.id) × (_root_.List SpecTec.parameterIR))))))))))))) | [] => .unmatch)


noncomputable def «$align_parameterListIR_given:case_3:pattern-iter:0_clauses» (input0 : (_root_.List (pair _root_.String parameterIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_3:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_3:pattern-iter:0:clause:1»  input0)]


noncomputable def «$align_parameterListIR_given:case_3:iter:2:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String parameterIR))) : (_root_.List (pair _root_.String parameterIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$align_parameterListIR_given:case_3:iter:2:clause:1» (input0 : (_root_.List SpecTec.id)) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id : SpecTec.id := «exec:2»; (let «tail:0» : (_root_.List SpecTec.id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let parameterIR : SpecTec.parameterIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.parameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String SpecTec.parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_3:iter:2» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String SpecTec.parameterIR))) => (let «tail:2» : (_root_.List (pair _root_.String SpecTec.parameterIR)) := «exec:5»; (.pure (((((pair.«% ':' %» id parameterIR) : (pair SpecTec.id SpecTec.parameterIR)) :: «tail:2») : (_root_.List (pair _root_.String SpecTec.parameterIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$align_parameterListIR_given:case_3:iter:2_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_3:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_3:iter:2:clause:1»  input0 input1)]


noncomputable def «$align_parameterListIR_given:case_4:pattern-iter:0:clause:0» (input0 : (_root_.List (pair _root_.String parameterIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List id)), ([] : (_root_.List parameterIR))) : ((_root_.List id) × (_root_.List parameterIR))))) | _ :: _ => .unmatch)


noncomputable def «$align_parameterListIR_given:case_4:pattern-iter:0:clause:1» (input0 : (_root_.List (pair _root_.String SpecTec.parameterIR))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let id : SpecTec.id := «exec:3»; (let parameterIR : SpecTec.parameterIR := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair _root_.String SpecTec.parameterIR)) := «exec:1»; (.bind (.call ⟨((_root_.List SpecTec.id) × (_root_.List SpecTec.parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_4:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List SpecTec.id) × (_root_.List SpecTec.parameterIR))) => (let «pattern-tail:1» : (_root_.List SpecTec.id) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List SpecTec.parameterIR) := («exec:5»).2; (.pure ((((id :: «pattern-tail:1»), (parameterIR :: «pattern-tail:2»)) : ((_root_.List SpecTec.id) × (_root_.List SpecTec.parameterIR))))))))))))) | [] => .unmatch)


noncomputable def «$align_parameterListIR_given:case_4:pattern-iter:0_clauses» (input0 : (_root_.List (pair _root_.String parameterIR))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_4:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_4:pattern-iter:0:clause:1»  input0)]


noncomputable def «$align_parameterListIR_given:case_4:iter:2:clause:0» (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair _root_.String parameterIR))) : (_root_.List (pair _root_.String parameterIR))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$align_parameterListIR_given:case_4:iter:2:clause:1» (input0 : (_root_.List SpecTec.id)) (input1 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let id : SpecTec.id := «exec:2»; (let «tail:0» : (_root_.List SpecTec.id) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let parameterIR : SpecTec.parameterIR := «exec:4»; (let «tail:1» : (_root_.List SpecTec.parameterIR) := «exec:3»; (.bind (.call ⟨(_root_.List (pair _root_.String SpecTec.parameterIR)), SpecTecCall.«$align_parameterListIR_given:case_4:iter:2» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair _root_.String SpecTec.parameterIR))) => (let «tail:2» : (_root_.List (pair _root_.String SpecTec.parameterIR)) := «exec:5»; (.pure (((((pair.«% ':' %» id parameterIR) : (pair SpecTec.id SpecTec.parameterIR)) :: «tail:2») : (_root_.List (pair _root_.String SpecTec.parameterIR)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$align_parameterListIR_given:case_4:iter:2_clauses» (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_4:iter:2:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$align_parameterListIR_given:case_4:iter:2:clause:1»  input0 input1)]

end SpecTec
