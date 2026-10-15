import SpecTecDecl0316

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_typeDeclarationIR:clause:3» (input0 : SpecTec.typeDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDeclarationIR : SpecTec.typeDeclarationIR := input0; (.bind (.guard (((«sub:typeDeclarationIR:controlTypeDeclarationIR» typeDeclarationIR) = true))) (fun (_ : Unit) => (match («$lift_typeDeclarationIR:case_4:downcast:0» typeDeclarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.controlTypeDeclarationIR := «exec:1»; (let controlTypeDeclarationIR : SpecTec.controlTypeDeclarationIR := «eval:0»; (.bind (.call ⟨controlTypeDeclaration, SpecTecCall.«$lift_controlTypeDeclarationIR» controlTypeDeclarationIR⟩) (fun («exec:2» : controlTypeDeclaration) => (let «eval:1» : controlTypeDeclaration := «exec:2»; (.pure (((«cast:controlTypeDeclaration:typeDeclaration» «eval:1») : typeDeclaration)))))))) | none => .unmatch))))


noncomputable def «$lift_typeDeclarationIR:clause:4» (input0 : SpecTec.typeDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDeclarationIR : SpecTec.typeDeclarationIR := input0; (.bind (.guard (((«sub:typeDeclarationIR:packageTypeDeclarationIR» typeDeclarationIR) = true))) (fun (_ : Unit) => (match («$lift_typeDeclarationIR:case_5:downcast:0» typeDeclarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.packageTypeDeclarationIR := «exec:1»; (let packageTypeDeclarationIR : SpecTec.packageTypeDeclarationIR := «eval:0»; (.bind (.call ⟨packageTypeDeclaration, SpecTecCall.«$lift_packageTypeDeclarationIR» packageTypeDeclarationIR⟩) (fun («exec:2» : packageTypeDeclaration) => (let «eval:1» : packageTypeDeclaration := «exec:2»; (.pure (((«cast:packageTypeDeclaration:typeDeclaration» «eval:1») : typeDeclaration)))))))) | none => .unmatch))))


noncomputable def «$lift_typeDeclarationIR_clauses» (input0 : typeDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_typeDeclarationIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_typeDeclarationIR:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_typeDeclarationIR:clause:2»  input0), fun (_ : _root_.Unit) => («$lift_typeDeclarationIR:clause:3»  input0), fun (_ : _root_.Unit) => («$lift_typeDeclarationIR:clause:4»  input0)]


noncomputable def «$lift_declarationIR:clause:0» (input0 : SpecTec.declarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let declarationIR : SpecTec.declarationIR := input0; (.bind (.guard (((«sub:declarationIR:constantDeclarationIR» declarationIR) = true))) (fun (_ : Unit) => (match («$lift_declarationIR:case_1:downcast:0» declarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.constantDeclarationIR := «exec:1»; (let constantDeclarationIR : SpecTec.constantDeclarationIR := «eval:0»; (.bind (.call ⟨constantDeclaration, SpecTecCall.«$lift_constantDeclarationIR» constantDeclarationIR⟩) (fun («exec:2» : constantDeclaration) => (let «eval:1» : constantDeclaration := «exec:2»; (.pure (((«cast:constantDeclaration:declaration» «eval:1») : declaration)))))))) | none => .unmatch))))


noncomputable def «$lift_declarationIR:clause:1» (input0 : SpecTec.declarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let declarationIR : SpecTec.declarationIR := input0; (.bind (.guard (((«sub:declarationIR:instantiationIR» declarationIR) = true))) (fun (_ : Unit) => (match («$lift_declarationIR:case_2:downcast:0» declarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.instantiationIR := «exec:1»; (let instantiationIR : SpecTec.instantiationIR := «eval:0»; (.bind (.call ⟨instantiation, SpecTecCall.«$lift_instantiationIR» instantiationIR⟩) (fun («exec:2» : instantiation) => (let «eval:1» : instantiation := «exec:2»; (.pure (((«cast:instantiation:declaration» «eval:1») : declaration)))))))) | none => .unmatch))))


noncomputable def «$lift_declarationIR:clause:2» (input0 : SpecTec.declarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let declarationIR : SpecTec.declarationIR := input0; (.bind (.guard (((«sub:declarationIR:functionDeclarationIR» declarationIR) = true))) (fun (_ : Unit) => (match («$lift_declarationIR:case_3:downcast:0» declarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.functionDeclarationIR := «exec:1»; (let functionDeclarationIR : SpecTec.functionDeclarationIR := «eval:0»; (.bind (.call ⟨functionDeclaration, SpecTecCall.«$lift_functionDeclarationIR» functionDeclarationIR⟩) (fun («exec:2» : functionDeclaration) => (let «eval:1» : functionDeclaration := «exec:2»; (.pure (((«cast:functionDeclaration:declaration» «eval:1») : declaration)))))))) | none => .unmatch))))


noncomputable def «$lift_declarationIR:clause:3» (input0 : SpecTec.declarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let declarationIR : SpecTec.declarationIR := input0; (.bind (.guard (((«sub:declarationIR:actionDeclarationIR» declarationIR) = true))) (fun (_ : Unit) => (match («$lift_declarationIR:case_4:downcast:0» declarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.actionDeclarationIR := «exec:1»; (let actionDeclarationIR : SpecTec.actionDeclarationIR := «eval:0»; (.bind (.call ⟨actionDeclaration, SpecTecCall.«$lift_actionDeclarationIR» actionDeclarationIR⟩) (fun («exec:2» : actionDeclaration) => (let «eval:1» : actionDeclaration := «exec:2»; (.pure (((«cast:actionDeclaration:declaration» «eval:1») : declaration)))))))) | none => .unmatch))))


noncomputable def «$lift_declarationIR:clause:4» (input0 : SpecTec.declarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let declarationIR : SpecTec.declarationIR := input0; (.bind (.guard (((«sub:declarationIR:errorDeclarationIR» declarationIR) = true))) (fun (_ : Unit) => (match («$lift_declarationIR:case_5:downcast:0» declarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.errorDeclarationIR := «exec:1»; (let errorDeclarationIR : SpecTec.errorDeclarationIR := «eval:0»; (.bind (.call ⟨errorDeclaration, SpecTecCall.«$lift_errorDeclarationIR» errorDeclarationIR⟩) (fun («exec:2» : errorDeclaration) => (let «eval:1» : errorDeclaration := «exec:2»; (.pure (((«cast:errorDeclaration:declaration» «eval:1») : declaration)))))))) | none => .unmatch))))


noncomputable def «$lift_declarationIR:clause:5» (input0 : SpecTec.declarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let declarationIR : SpecTec.declarationIR := input0; (.bind (.guard (((«sub:declarationIR:matchKindDeclarationIR» declarationIR) = true))) (fun (_ : Unit) => (match («$lift_declarationIR:case_6:downcast:0» declarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.matchKindDeclarationIR := «exec:1»; (let matchKindDeclarationIR : SpecTec.matchKindDeclarationIR := «eval:0»; (.bind (.call ⟨matchKindDeclaration, SpecTecCall.«$lift_matchKindDeclarationIR» matchKindDeclarationIR⟩) (fun («exec:2» : matchKindDeclaration) => (let «eval:1» : matchKindDeclaration := «exec:2»; (.pure (((«cast:matchKindDeclaration:declaration» «eval:1») : declaration)))))))) | none => .unmatch))))


noncomputable def «$lift_declarationIR:clause:6» (input0 : SpecTec.declarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let declarationIR : SpecTec.declarationIR := input0; (.bind (.guard (((«sub:declarationIR:externDeclarationIR» declarationIR) = true))) (fun (_ : Unit) => (match («$lift_declarationIR:case_7:downcast:0» declarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.externDeclarationIR := «exec:1»; (let externDeclarationIR : SpecTec.externDeclarationIR := «eval:0»; (.bind (.call ⟨externDeclaration, SpecTecCall.«$lift_externDeclarationIR» externDeclarationIR⟩) (fun («exec:2» : externDeclaration) => (let «eval:1» : externDeclaration := «exec:2»; (.pure (((«cast:externDeclaration:declaration» «eval:1») : declaration)))))))) | none => .unmatch))))


noncomputable def «$lift_declarationIR:clause:7» (input0 : SpecTec.declarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let declarationIR : SpecTec.declarationIR := input0; (.bind (.guard (((«sub:declarationIR:parserDeclarationIR» declarationIR) = true))) (fun (_ : Unit) => (match («$lift_declarationIR:case_8:downcast:0» declarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.parserDeclarationIR := «exec:1»; (let parserDeclarationIR : SpecTec.parserDeclarationIR := «eval:0»; (.bind (.call ⟨parserDeclaration, SpecTecCall.«$lift_parserDeclarationIR» parserDeclarationIR⟩) (fun («exec:2» : parserDeclaration) => (let «eval:1» : parserDeclaration := «exec:2»; (.pure (((«cast:parserDeclaration:declaration» «eval:1») : declaration)))))))) | none => .unmatch))))


noncomputable def «$lift_declarationIR:clause:8» (input0 : SpecTec.declarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let declarationIR : SpecTec.declarationIR := input0; (.bind (.guard (((«sub:declarationIR:controlDeclarationIR» declarationIR) = true))) (fun (_ : Unit) => (match («$lift_declarationIR:case_9:downcast:0» declarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.controlDeclarationIR := «exec:1»; (let controlDeclarationIR : SpecTec.controlDeclarationIR := «eval:0»; (.bind (.call ⟨controlDeclaration, SpecTecCall.«$lift_controlDeclarationIR» controlDeclarationIR⟩) (fun («exec:2» : controlDeclaration) => (let «eval:1» : controlDeclaration := «exec:2»; (.pure (((«cast:controlDeclaration:declaration» «eval:1») : declaration)))))))) | none => .unmatch))))


noncomputable def «$lift_declarationIR:clause:9» (input0 : SpecTec.declarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let declarationIR : SpecTec.declarationIR := input0; (.bind (.guard (((«sub:declarationIR:typeDeclarationIR» declarationIR) = true))) (fun (_ : Unit) => (match («$lift_declarationIR:case_10:downcast:0» declarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.typeDeclarationIR := «exec:1»; (let typeDeclarationIR : SpecTec.typeDeclarationIR := «eval:0»; (.bind (.call ⟨typeDeclaration, SpecTecCall.«$lift_typeDeclarationIR» typeDeclarationIR⟩) (fun («exec:2» : typeDeclaration) => (let «eval:1» : typeDeclaration := «exec:2»; (.pure (((«cast:typeDeclaration:declaration» «eval:1») : declaration)))))))) | none => .unmatch))))


noncomputable def «$lift_declarationIR:clause:10» (input0 : SpecTec.declarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let declarationIR : SpecTec.declarationIR := input0; (.bind (.call ⟨declaration, SpecTecCall.«$sink» declaration⟩) (fun («exec:1» : declaration) => (let «eval:0» : declaration := «exec:1»; (.pure ((«eval:0» : declaration)))))))


noncomputable def «$lift_declarationIR_clauses» (input0 : declarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_declarationIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_declarationIR:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_declarationIR:clause:2»  input0), fun (_ : _root_.Unit) => («$lift_declarationIR:clause:3»  input0), fun (_ : _root_.Unit) => («$lift_declarationIR:clause:4»  input0), fun (_ : _root_.Unit) => («$lift_declarationIR:clause:5»  input0), fun (_ : _root_.Unit) => («$lift_declarationIR:clause:6»  input0), fun (_ : _root_.Unit) => («$lift_declarationIR:clause:7»  input0), fun (_ : _root_.Unit) => («$lift_declarationIR:clause:8»  input0), fun (_ : _root_.Unit) => («$lift_declarationIR:clause:9»  input0), fun (_ : _root_.Unit) => («$lift_declarationIR:clause:10»  input0)]


noncomputable def «$lift_p4programIR:case_1:iter:0:clause:0» (input0 : (_root_.List declarationIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List declaration)) : (_root_.List declaration)))) | _ :: _ => .unmatch)


noncomputable def «$lift_p4programIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.declarationIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let declarationIR : SpecTec.declarationIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.declarationIR) := «exec:1»; (.bind (.call ⟨SpecTec.declaration, SpecTecCall.«$lift_declarationIR» declarationIR⟩) (fun («exec:3» : SpecTec.declaration) => (let «eval:1» : SpecTec.declaration := «exec:3»; (let declaration : SpecTec.declaration := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.declaration), SpecTecCall.«$lift_p4programIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.declaration)) => (let «tail:1» : (_root_.List SpecTec.declaration) := «exec:4»; (.pure (((declaration :: «tail:1») : (_root_.List SpecTec.declaration))))))))))))) | [] => .unmatch)


noncomputable def «$lift_p4programIR:case_1:iter:0_clauses» (input0 : (_root_.List declarationIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_p4programIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_p4programIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_p4programIR:clause:0» (input0 : p4programIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% ';'» «exec:1» => (let «declarationIR*» : (_root_.List declarationIR) := «exec:1»; (.bind (.call ⟨(_root_.List declaration), SpecTecCall.«$lift_p4programIR:case_1:iter:0» «declarationIR*»⟩) (fun («exec:2» : (_root_.List declaration)) => (let «declaration*» : (_root_.List declaration) := «exec:2»; (.bind (.call ⟨p4program, SpecTecCall.«$unflatten_p4program» «declaration*»⟩) (fun («exec:3» : p4program) => (let «eval:2» : p4program := «exec:3»; (.pure ((«eval:2» : p4program)))))))))))


noncomputable def «$lift_p4programIR_clauses» (input0 : p4programIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_p4programIR:clause:0»  input0)]


noncomputable def «$un_lnot:clause:0» (input0 : SpecTec.value) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let value : SpecTec.value := input0; (.bind (.guard (((«sub:value:boolValue» value) = true))) (fun (_ : Unit) => (match («$un_lnot:case_1:downcast:0» value) with | some «exec:1» => (let «eval:0» : boolValue := «exec:1»; (match «eval:0» with | ._B «exec:2» => (let b : _root_.Bool := «exec:2»; (.pure ((((SpecTec.value._B (!b)) : SpecTec.value) : SpecTec.value)))))) | none => .unmatch))))


noncomputable def «$un_lnot_clauses» (input0 : value) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$un_lnot:clause:0»  input0)]


noncomputable def «$largest_priority_wins:clause:0» (input0 : tableObjectProperty) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBL : tableObjectProperty := input0; (let «tableCustomPropertyIR*» : (_root_.List tableCustomPropertyIR) := (tableObjectProperty.CUSTOMS TBL); (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$largest_priority_wins:case_1:iter:0» «tableCustomPropertyIR*»⟩) (fun («exec:1» : (_root_.List _root_.Bool)) => (let «eval:2» : (_root_.List _root_.Bool) := «exec:1»; (.bind (.call ⟨(_root_.List tableCustomPropertyIR), SpecTecCall.«$filter_» tableCustomPropertyIR «tableCustomPropertyIR*» «eval:2»⟩) (fun («exec:2» : (_root_.List tableCustomPropertyIR)) => (let «eval:3» : (_root_.List tableCustomPropertyIR) := «exec:2»; (let «tableCustomPropertyIR''*» : (_root_.List tableCustomPropertyIR) := «eval:3»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableCustomPropertyIR''*») = (1 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tableCustomPropertyIR''*» with | «exec:4» :: «exec:3» => (let tableCustomPropertyIR' : tableCustomPropertyIR := «exec:4»; (match «exec:3» with | [] => (.bind (.guard (((«exec:match:tableCustomPropertyIR:% % CUSTOM_CONST % % ';'» tableCustomPropertyIR') = true))) (fun (_ : Unit) => (match tableCustomPropertyIR' with | .«% % CUSTOM_CONST % % ';'» «exec:5» «exec:6» «exec:7» «exec:8» => (let _annotationList : annotationList := «exec:5»; (let _constOptIR : constOptIR := «exec:6»; (let _nameIR : nameIR := «exec:7»; (match «exec:8» with | .«'=' _VALUE %» «exec:9» => (let value : SpecTec.value := «exec:9»; (.bind (.guard (((«sub:value:boolValue» value) = true))) (fun (_ : Unit) => (match («$largest_priority_wins:case_1:downcast:4» value) with | some «exec:10» => (let «eval:4» : boolValue := «exec:10»; (match «eval:4» with | ._B «exec:11» => (let b : _root_.Bool := «exec:11»; (.pure ((b : _root_.Bool)))))) | none => .unmatch)))))))) | _ => .unmatch))) | _ :: _ => .unmatch)) | [] => .unmatch))))))))))))


noncomputable def «$largest_priority_wins:clause:1» (input0 : tableObjectProperty) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBL : tableObjectProperty := input0; (let «tableCustomPropertyIR*» : (_root_.List tableCustomPropertyIR) := (tableObjectProperty.CUSTOMS TBL); (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$largest_priority_wins:case_2:iter:0» «tableCustomPropertyIR*»⟩) (fun («exec:1» : (_root_.List _root_.Bool)) => (let «eval:2» : (_root_.List _root_.Bool) := «exec:1»; (.bind (.call ⟨(_root_.List tableCustomPropertyIR), SpecTecCall.«$filter_» tableCustomPropertyIR «tableCustomPropertyIR*» «eval:2»⟩) (fun («exec:2» : (_root_.List tableCustomPropertyIR)) => (let «eval:3» : (_root_.List tableCustomPropertyIR) := «exec:2»; (match «eval:3» with | [] => (.pure ((true : _root_.Bool))) | _ :: _ => .unmatch)))))))))


noncomputable def «$largest_priority_wins_clauses» (input0 : tableObjectProperty) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$largest_priority_wins:clause:0»  input0), fun (_ : _root_.Unit) => («$largest_priority_wins:clause:1»  input0)]


noncomputable def «$select_action:clause:0» (input0 : tableObjectProperty) (input1 : (_root_.List tableMatch)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBL : tableObjectProperty := input0; (let «tableMatch*» : (_root_.List tableMatch) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableMatch*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match (tableObjectProperty.DEFAULT_ACTION TBL) with | .«% % DEFAULT_ACTION '=' % ';'» «exec:1» «exec:2» «exec:3» => (let _annotationList : annotationList := «exec:1»; (let _constOptIR : constOptIR := «exec:2»; (let tableActionReferenceIR : SpecTec.tableActionReferenceIR := «exec:3»; (.pure ((tableActionReferenceIR : SpecTec.tableActionReferenceIR)))))))))))


noncomputable def «$select_action:clause:1» (input0 : tableObjectProperty) (input1 : (_root_.List SpecTec.tableMatch)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBL : tableObjectProperty := input0; (let «tableMatch'*» : (_root_.List SpecTec.tableMatch) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableMatch'*») = (1 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tableMatch'*» with | «exec:2» :: «exec:1» => (let tableMatch : SpecTec.tableMatch := «exec:2»; (match «exec:1» with | [] => (match tableMatch with | .«% ':' %» «exec:3» «exec:4» => (let _nat? : (_root_.Option _root_.Nat) := «exec:3»; (let tableActionReferenceIR : SpecTec.tableActionReferenceIR := «exec:4»; (.pure ((tableActionReferenceIR : SpecTec.tableActionReferenceIR)))))) | _ :: _ => .unmatch)) | [] => .unmatch)))))


noncomputable def «$select_action:clause:2» (input0 : tableObjectProperty) (input1 : (_root_.List tableMatch)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBL : tableObjectProperty := input0; (let «tableMatch*» : (_root_.List tableMatch) := input1; (.bind (.guard (((_root_.List.length «tableMatch*») > (1 : _root_.Nat)))) (fun (_ : Unit) => (.bind (.call ⟨((_root_.List (_root_.Option _root_.Nat)) × (_root_.List tableActionReferenceIR)), SpecTecCall.«$select_action:case_3:iter:0» «tableMatch*»⟩) (fun («exec:1» : ((_root_.List (_root_.Option _root_.Nat)) × (_root_.List tableActionReferenceIR))) => (let «nat?*» : (_root_.List (_root_.Option _root_.Nat)) := («exec:1»).1; (let «tableActionReferenceIR*» : (_root_.List tableActionReferenceIR) := («exec:1»).2; (.bind (.call ⟨_root_.Unit, SpecTecCall.«$select_action:case_3:iter:1» «nat?*»⟩) (fun («exec:2» : _root_.Unit) => (.bind (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$select_action:case_3:iter:2» «nat?*»⟩) (fun («exec:3» : (_root_.List _root_.Nat)) => (let «n_priority*» : (_root_.List _root_.Nat) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.Nat × tableActionReferenceIR)), SpecTecCall.«$select_action:case_3:iter:3» «n_priority*» «tableActionReferenceIR*»⟩) (fun («exec:4» : (_root_.List (_root_.Nat × tableActionReferenceIR))) => (let «eval:4» : (_root_.List (_root_.Nat × tableActionReferenceIR)) := «exec:4»; (let «eval:6» : (_root_.List (_root_.Nat × tableActionReferenceIR)) := («$sort_» (X := tableActionReferenceIR) «eval:4»); (.bind (.call ⟨((_root_.List _root_.Nat) × (_root_.List tableActionReferenceIR)), SpecTecCall.«$select_action:case_3:pattern-iter:5» «eval:6»⟩) (fun («exec:5» : ((_root_.List _root_.Nat) × (_root_.List tableActionReferenceIR))) => (let «n_priority_sorted*» : (_root_.List _root_.Nat) := («exec:5»).1; (let «tableActionReferenceIR_sorted*» : (_root_.List tableActionReferenceIR) := («exec:5»).2; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$largest_priority_wins» TBL⟩) (fun («exec:6» : _root_.Bool) => (let «eval:7» : _root_.Bool := «exec:6»; (.bind (.guard ((«eval:7» = true))) (fun (_ : Unit) => (let «tableActionReferenceIR'*» : (_root_.List tableActionReferenceIR) := («$rev_» (X := tableActionReferenceIR) «tableActionReferenceIR_sorted*»); (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableActionReferenceIR'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tableActionReferenceIR'*» with | «exec:8» :: «exec:7» => (let tableActionReferenceIR_h : tableActionReferenceIR := «exec:8»; (let «_tableActionReferenceIR*» : (_root_.List tableActionReferenceIR) := «exec:7»; (.pure ((tableActionReferenceIR_h : tableActionReferenceIR))))) | [] => .unmatch))))))))))))))))))))))))))))))


noncomputable def «$select_action:clause:3» (input0 : tableObjectProperty) (input1 : (_root_.List tableMatch)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TBL : tableObjectProperty := input0; (let «tableMatch*» : (_root_.List tableMatch) := input1; (.bind (.guard (((_root_.List.length «tableMatch*») > (1 : _root_.Nat)))) (fun (_ : Unit) => (.bind (.call ⟨((_root_.List (_root_.Option _root_.Nat)) × (_root_.List tableActionReferenceIR)), SpecTecCall.«$select_action:case_4:iter:0» «tableMatch*»⟩) (fun («exec:1» : ((_root_.List (_root_.Option _root_.Nat)) × (_root_.List tableActionReferenceIR))) => (let «nat?*» : (_root_.List (_root_.Option _root_.Nat)) := («exec:1»).1; (let «tableActionReferenceIR*» : (_root_.List tableActionReferenceIR) := («exec:1»).2; (.bind (.call ⟨_root_.Unit, SpecTecCall.«$select_action:case_4:iter:1» «nat?*»⟩) (fun («exec:2» : _root_.Unit) => (.bind (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$select_action:case_4:iter:2» «nat?*»⟩) (fun («exec:3» : (_root_.List _root_.Nat)) => (let «n_priority*» : (_root_.List _root_.Nat) := «exec:3»; (.bind (.call ⟨(_root_.List (_root_.Nat × tableActionReferenceIR)), SpecTecCall.«$select_action:case_4:iter:3» «n_priority*» «tableActionReferenceIR*»⟩) (fun («exec:4» : (_root_.List (_root_.Nat × tableActionReferenceIR))) => (let «eval:4» : (_root_.List (_root_.Nat × tableActionReferenceIR)) := «exec:4»; (let «eval:6» : (_root_.List (_root_.Nat × tableActionReferenceIR)) := («$sort_» (X := tableActionReferenceIR) «eval:4»); (.bind (.call ⟨((_root_.List _root_.Nat) × (_root_.List tableActionReferenceIR)), SpecTecCall.«$select_action:case_4:pattern-iter:5» «eval:6»⟩) (fun («exec:5» : ((_root_.List _root_.Nat) × (_root_.List tableActionReferenceIR))) => (let «n_priority_sorted*» : (_root_.List _root_.Nat) := («exec:5»).1; (let «tableActionReferenceIR_sorted*» : (_root_.List tableActionReferenceIR) := («exec:5»).2; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$largest_priority_wins» TBL⟩) (fun («exec:6» : _root_.Bool) => (let «eval:7» : _root_.Bool := «exec:6»; (.bind (.guard ((¬ («eval:7» = true)))) (fun (_ : Unit) => (let «tableActionReferenceIR'*» : (_root_.List tableActionReferenceIR) := «tableActionReferenceIR_sorted*»; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableActionReferenceIR'*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tableActionReferenceIR'*» with | «exec:8» :: «exec:7» => (let tableActionReferenceIR_h : tableActionReferenceIR := «exec:8»; (let «_tableActionReferenceIR*» : (_root_.List tableActionReferenceIR) := «exec:7»; (.pure ((tableActionReferenceIR_h : tableActionReferenceIR))))) | [] => .unmatch))))))))))))))))))))))))))))))


noncomputable def «$select_action_clauses» (input0 : tableObjectProperty) (input1 : (_root_.List tableMatch)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$select_action:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$select_action:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$select_action:clause:2»  input0 input1), fun (_ : _root_.Unit) => («$select_action:clause:3»  input0 input1)]


noncomputable def «$cast_control_plane:case_3:iter:4:clause:0» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$cast_control_plane:case_3:iter:4:clause:1» (input0 : (_root_.List value)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let value_frame : value := «exec:2»; (let «tail:0» : (_root_.List value) := «exec:1»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$cast_control_plane:case_3:iter:4» «tail:0»⟩) (fun («exec:3» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:3»; (.pure ((((«sub:value:errorValue» value_frame) :: «tail:1») : (_root_.List _root_.Bool))))))))) | [] => .unmatch)

end SpecTec
