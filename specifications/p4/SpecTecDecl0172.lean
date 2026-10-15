import SpecTecDecl0171

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «CallableType_wf:controlApplyMethodTypeIR:iter:4_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («CallableType_wf:controlApplyMethodTypeIR:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («CallableType_wf:controlApplyMethodTypeIR:iter:4:clause:1»  input0)]


noncomputable def «ConstructorType_wf:externObjectTypeIR:iter:3:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List id)), (([] : (_root_.List parameterInitializerOptIR)), ([] : (_root_.List typeIR)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))))) | _ :: _ => .unmatch)


noncomputable def «ConstructorType_wf:externObjectTypeIR:iter:3:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (match parameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let typeIR : SpecTec.typeIR := «exec:5»; (let _id : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))), SpecTecCall.«ConstructorType_wf:externObjectTypeIR:iter:3» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List id) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List parameterInitializerOptIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List SpecTec.typeIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_id :: «tail:3»), ((_parameterInitializerOptIR :: «tail:4»), (typeIR :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «ConstructorType_wf:externObjectTypeIR:iter:3_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («ConstructorType_wf:externObjectTypeIR:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («ConstructorType_wf:externObjectTypeIR:iter:3:clause:1»  input0)]


noncomputable def «ConstructorType_wf:parserObjectTypeIR:iter:5:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List id)), (([] : (_root_.List parameterInitializerOptIR)), ([] : (_root_.List typeIR)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))))) | _ :: _ => .unmatch)


noncomputable def «ConstructorType_wf:parserObjectTypeIR:iter:5:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (match parameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let typeIR : SpecTec.typeIR := «exec:5»; (let _id : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))), SpecTecCall.«ConstructorType_wf:parserObjectTypeIR:iter:5» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List id) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List parameterInitializerOptIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List SpecTec.typeIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_id :: «tail:3»), ((_parameterInitializerOptIR :: «tail:4»), (typeIR :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «ConstructorType_wf:parserObjectTypeIR:iter:5_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («ConstructorType_wf:parserObjectTypeIR:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («ConstructorType_wf:parserObjectTypeIR:iter:5:clause:1»  input0)]


noncomputable def «ConstructorType_wf:controlObjectTypeIR:iter:5:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List id)), (([] : (_root_.List parameterInitializerOptIR)), ([] : (_root_.List typeIR)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))))) | _ :: _ => .unmatch)


noncomputable def «ConstructorType_wf:controlObjectTypeIR:iter:5:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (match parameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let typeIR : SpecTec.typeIR := «exec:5»; (let _id : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))), SpecTecCall.«ConstructorType_wf:controlObjectTypeIR:iter:5» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List id) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List parameterInitializerOptIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List SpecTec.typeIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_id :: «tail:3»), ((_parameterInitializerOptIR :: «tail:4»), (typeIR :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «ConstructorType_wf:controlObjectTypeIR:iter:5_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («ConstructorType_wf:controlObjectTypeIR:iter:5:clause:0»  input0), fun (_ : _root_.Unit) => («ConstructorType_wf:controlObjectTypeIR:iter:5:clause:1»  input0)]


noncomputable def «ConstructorType_wf:packageObjectTypeIR:iter:3:clause:0» (input0 : (_root_.List parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List annotationList)), (([] : (_root_.List direction)), (([] : (_root_.List id)), (([] : (_root_.List parameterInitializerOptIR)), ([] : (_root_.List typeIR)))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))))) | _ :: _ => .unmatch)


noncomputable def «ConstructorType_wf:packageObjectTypeIR:iter:3:clause:1» (input0 : (_root_.List SpecTec.parameterIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let parameterIR : SpecTec.parameterIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.parameterIR) := «exec:1»; (match parameterIR with | .«% % % % %» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» => (let _annotationList : annotationList := «exec:3»; (let _direction : direction := «exec:4»; (let typeIR : SpecTec.typeIR := «exec:5»; (let _id : id := «exec:6»; (let _parameterInitializerOptIR : parameterInitializerOptIR := «exec:7»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))), SpecTecCall.«ConstructorType_wf:packageObjectTypeIR:iter:3» «tail:0»⟩) (fun («exec:8» : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR)))))) => (let «tail:1» : (_root_.List annotationList) := («exec:8»).1; (let «tail:2» : (_root_.List direction) := ((«exec:8»).2).1; (let «tail:3» : (_root_.List id) := (((«exec:8»).2).2).1; (let «tail:4» : (_root_.List parameterInitializerOptIR) := ((((«exec:8»).2).2).2).1; (let «tail:5» : (_root_.List SpecTec.typeIR) := ((((«exec:8»).2).2).2).2; (.pure ((((_annotationList :: «tail:1»), ((_direction :: «tail:2»), ((_id :: «tail:3»), ((_parameterInitializerOptIR :: «tail:4»), (typeIR :: «tail:5»))))) : ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List SpecTec.typeIR))))))))))))))))))))))) | [] => .unmatch)


noncomputable def «ConstructorType_wf:packageObjectTypeIR:iter:3_clauses» (input0 : (_root_.List parameterIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («ConstructorType_wf:packageObjectTypeIR:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («ConstructorType_wf:packageObjectTypeIR:iter:3:clause:1»  input0)]


noncomputable def «$nestable_typedef:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .BOOL  => (.bind (.guard ((0 : _root_.Nat) = («$nestable_typedef:matches:0:row» ((typeIR.BOOL) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$nestable_typedef:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .ERROR  => (.bind (.guard ((0 : _root_.Nat) = («$nestable_typedef:matches:1:row» ((typeIR.ERROR) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$nestable_typedef:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .STRING  => (.bind (.guard ((0 : _root_.Nat) = («$nestable_typedef:matches:2:row» ((typeIR.STRING) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$nestable_typedef:clause:3» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let integerTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_typedef:matches:3:row» integerTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_typedef:clause:4» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_typedef:matches:4:row» nameTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_typedef:clause:5» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_typedef:matches:5:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_typedef» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$nestable_typedef:clause:6» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let newTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_typedef:matches:6:row» newTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_typedef:clause:7» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let dataTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_typedef:matches:7:row» dataTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_typedef:clause:8» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externObjectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_typedef:matches:8:row» externObjectTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_typedef:clause:9» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let parserObjectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_typedef:matches:9:row» parserObjectTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_typedef:clause:10» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let controlObjectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_typedef:matches:10:row» controlObjectTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_typedef:clause:11» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let packageObjectTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_typedef:matches:11:row» packageObjectTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_typedef:clause:12» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_typedef:matches:12:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$nestable_typedef_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$nestable_typedef:clause:0»  input0), fun (_ : _root_.Unit) => («$nestable_typedef:clause:1»  input0), fun (_ : _root_.Unit) => («$nestable_typedef:clause:2»  input0), fun (_ : _root_.Unit) => («$nestable_typedef:clause:3»  input0), fun (_ : _root_.Unit) => («$nestable_typedef:clause:4»  input0), fun (_ : _root_.Unit) => («$nestable_typedef:clause:5»  input0), fun (_ : _root_.Unit) => («$nestable_typedef:clause:6»  input0), fun (_ : _root_.Unit) => («$nestable_typedef:clause:7»  input0), fun (_ : _root_.Unit) => («$nestable_typedef:clause:8»  input0), fun (_ : _root_.Unit) => («$nestable_typedef:clause:9»  input0), fun (_ : _root_.Unit) => («$nestable_typedef:clause:10»  input0), fun (_ : _root_.Unit) => («$nestable_typedef:clause:11»  input0), fun (_ : _root_.Unit) => («$nestable_typedef:clause:12»  input0)]


noncomputable def «$nestable_new:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .BOOL  => (.bind (.guard ((0 : _root_.Nat) = («$nestable_new:matches:0:row» ((typeIR.BOOL) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$nestable_new:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_new:matches:1:row» ((typeIR.«BIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$nestable_new:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_new:matches:2:row» ((typeIR.«INT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$nestable_new:clause:3» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_new:matches:3:row» nameTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_new:clause:4» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_new:matches:4:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_new» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)

end SpecTec
