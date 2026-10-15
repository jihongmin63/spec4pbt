import SpecTecDecl0166

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_tableEntryPriorityIR_clauses» (input0 : tableEntryPriorityIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_tableEntryPriorityIR:clause:0»  input0)]


noncomputable def «$unflatten_tableEntryList':clause:0» (input0 : SpecTec.tableEntryList) (input1 : (_root_.List tableEntry)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableEntryList : SpecTec.tableEntryList := input0; (let «tableEntry*» : (_root_.List tableEntry) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableEntry*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((tableEntryList : SpecTec.tableEntryList)))))))


noncomputable def «$unflatten_tableEntryList':clause:1» (input0 : SpecTec.tableEntryList) (input1 : (_root_.List tableEntry)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableEntryList : SpecTec.tableEntryList := input0; (let «tableEntry*» : (_root_.List tableEntry) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableEntry*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tableEntry*» with | «exec:2» :: «exec:1» => (let tableEntry_h : tableEntry := «exec:2»; (let «tableEntry_t*» : (_root_.List tableEntry) := «exec:1»; (.bind (.call ⟨SpecTec.tableEntryList, SpecTecCall.«$unflatten_tableEntryList'» ((SpecTec.tableEntryList.«% %» tableEntryList tableEntry_h) : SpecTec.tableEntryList) «tableEntry_t*»⟩) (fun («exec:3» : SpecTec.tableEntryList) => (let «eval:0» : SpecTec.tableEntryList := «exec:3»; (.pure ((«eval:0» : SpecTec.tableEntryList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_tableEntryList'_clauses» (input0 : tableEntryList) (input1 : (_root_.List tableEntry)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_tableEntryList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_tableEntryList':clause:1»  input0 input1)]


noncomputable def «$unflatten_tableEntryList:clause:0» (input0 : (_root_.List tableEntry)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «tableEntry*» : (_root_.List tableEntry) := input0; (.bind (.call ⟨tableEntryList, SpecTecCall.«$unflatten_tableEntryList'» ((tableEntryList._EMPTY) : tableEntryList) «tableEntry*»⟩) (fun («exec:1» : tableEntryList) => (let «eval:0» : tableEntryList := «exec:1»; (.pure ((«eval:0» : tableEntryList)))))))


noncomputable def «$unflatten_tableEntryList_clauses» (input0 : (_root_.List tableEntry)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_tableEntryList:clause:0»  input0)]


noncomputable def «$unflatten_tablePropertyList':clause:0» (input0 : SpecTec.tablePropertyList) (input1 : (_root_.List tableProperty)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tablePropertyList : SpecTec.tablePropertyList := input0; (let «tableProperty*» : (_root_.List tableProperty) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableProperty*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((tablePropertyList : SpecTec.tablePropertyList)))))))


noncomputable def «$unflatten_tablePropertyList':clause:1» (input0 : SpecTec.tablePropertyList) (input1 : (_root_.List tableProperty)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tablePropertyList : SpecTec.tablePropertyList := input0; (let «tableProperty*» : (_root_.List tableProperty) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «tableProperty*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «tableProperty*» with | «exec:2» :: «exec:1» => (let tableProperty_h : tableProperty := «exec:2»; (let «tableProperty_t*» : (_root_.List tableProperty) := «exec:1»; (.bind (.call ⟨SpecTec.tablePropertyList, SpecTecCall.«$unflatten_tablePropertyList'» ((SpecTec.tablePropertyList.«% %» tablePropertyList tableProperty_h) : SpecTec.tablePropertyList) «tableProperty_t*»⟩) (fun («exec:3» : SpecTec.tablePropertyList) => (let «eval:0» : SpecTec.tablePropertyList := «exec:3»; (.pure ((«eval:0» : SpecTec.tablePropertyList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_tablePropertyList'_clauses» (input0 : tablePropertyList) (input1 : (_root_.List tableProperty)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_tablePropertyList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_tablePropertyList':clause:1»  input0 input1)]


noncomputable def «$unflatten_tablePropertyList:clause:0» (input0 : (_root_.List tableProperty)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «tableProperty*» : (_root_.List tableProperty) := input0; (.bind (.call ⟨tablePropertyList, SpecTecCall.«$unflatten_tablePropertyList'» ((tablePropertyList._EMPTY) : tablePropertyList) «tableProperty*»⟩) (fun («exec:1» : tablePropertyList) => (let «eval:0» : tablePropertyList := «exec:1»; (.pure ((«eval:0» : tablePropertyList)))))))


noncomputable def «$unflatten_tablePropertyList_clauses» (input0 : (_root_.List tableProperty)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_tablePropertyList:clause:0»  input0)]


noncomputable def «$unflatten_controlLocalDeclarationList':clause:0» (input0 : SpecTec.controlLocalDeclarationList) (input1 : (_root_.List controlLocalDeclaration)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let controlLocalDeclarationList : SpecTec.controlLocalDeclarationList := input0; (let «controlLocalDeclaration*» : (_root_.List controlLocalDeclaration) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «controlLocalDeclaration*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((controlLocalDeclarationList : SpecTec.controlLocalDeclarationList)))))))


noncomputable def «$unflatten_controlLocalDeclarationList':clause:1» (input0 : SpecTec.controlLocalDeclarationList) (input1 : (_root_.List controlLocalDeclaration)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let controlLocalDeclarationList : SpecTec.controlLocalDeclarationList := input0; (let «controlLocalDeclaration*» : (_root_.List controlLocalDeclaration) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «controlLocalDeclaration*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «controlLocalDeclaration*» with | «exec:2» :: «exec:1» => (let controlLocalDeclaration_h : controlLocalDeclaration := «exec:2»; (let «controlLocalDeclaration_t*» : (_root_.List controlLocalDeclaration) := «exec:1»; (.bind (.call ⟨SpecTec.controlLocalDeclarationList, SpecTecCall.«$unflatten_controlLocalDeclarationList'» ((SpecTec.controlLocalDeclarationList.«% %» controlLocalDeclarationList controlLocalDeclaration_h) : SpecTec.controlLocalDeclarationList) «controlLocalDeclaration_t*»⟩) (fun («exec:3» : SpecTec.controlLocalDeclarationList) => (let «eval:0» : SpecTec.controlLocalDeclarationList := «exec:3»; (.pure ((«eval:0» : SpecTec.controlLocalDeclarationList)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_controlLocalDeclarationList'_clauses» (input0 : controlLocalDeclarationList) (input1 : (_root_.List controlLocalDeclaration)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_controlLocalDeclarationList':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_controlLocalDeclarationList':clause:1»  input0 input1)]


noncomputable def «$unflatten_controlLocalDeclarationList:clause:0» (input0 : (_root_.List controlLocalDeclaration)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «controlLocalDeclaration*» : (_root_.List controlLocalDeclaration) := input0; (.bind (.call ⟨controlLocalDeclarationList, SpecTecCall.«$unflatten_controlLocalDeclarationList'» ((controlLocalDeclarationList._EMPTY) : controlLocalDeclarationList) «controlLocalDeclaration*»⟩) (fun («exec:1» : controlLocalDeclarationList) => (let «eval:0» : controlLocalDeclarationList := «exec:1»; (.pure ((«eval:0» : controlLocalDeclarationList)))))))


noncomputable def «$unflatten_controlLocalDeclarationList_clauses» (input0 : (_root_.List controlLocalDeclaration)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_controlLocalDeclarationList:clause:0»  input0)]


noncomputable def «$unflatten_p4program':clause:0» (input0 : SpecTec.p4program) (input1 : (_root_.List declaration)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p4program : SpecTec.p4program := input0; (let «declaration*» : (_root_.List declaration) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «declaration*») = (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (.pure ((p4program : SpecTec.p4program)))))))


noncomputable def «$unflatten_p4program':clause:1» (input0 : SpecTec.p4program) (input1 : (_root_.List declaration)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p4program : SpecTec.p4program := input0; (let «declaration*» : (_root_.List declaration) := input1; (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «declaration*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «declaration*» with | «exec:2» :: «exec:1» => (let declaration_h : declaration := «exec:2»; (let «declaration_t*» : (_root_.List declaration) := «exec:1»; (.bind (.call ⟨SpecTec.p4program, SpecTecCall.«$unflatten_p4program'» ((SpecTec.p4program.«% %» p4program declaration_h) : SpecTec.p4program) «declaration_t*»⟩) (fun («exec:3» : SpecTec.p4program) => (let «eval:0» : SpecTec.p4program := «exec:3»; (.pure ((«eval:0» : SpecTec.p4program)))))))) | [] => .unmatch)))))


noncomputable def «$unflatten_p4program'_clauses» (input0 : p4program) (input1 : (_root_.List declaration)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_p4program':clause:0»  input0 input1), fun (_ : _root_.Unit) => («$unflatten_p4program':clause:1»  input0 input1)]


noncomputable def «$unflatten_p4program:clause:0» (input0 : (_root_.List declaration)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «declaration*» : (_root_.List declaration) := input0; (.bind (.call ⟨p4program, SpecTecCall.«$unflatten_p4program'» ((p4program._EMPTY) : p4program) «declaration*»⟩) (fun («exec:1» : p4program) => (let «eval:0» : p4program := «exec:1»; (.pure ((«eval:0» : p4program)))))))


noncomputable def «$unflatten_p4program_clauses» (input0 : (_root_.List declaration)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$unflatten_p4program:clause:0»  input0)]


noncomputable def «$empty_typeFrame:clause:0»  : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (.bind (.call ⟨(map id varTypeIR), SpecTecCall.«$empty_map» id varTypeIR⟩) (fun («exec:1» : (map id varTypeIR)) => (let «eval:0» : (map id varTypeIR) := «exec:1»; (.pure ((«eval:0» : typeFrame))))))


noncomputable def «$empty_typeFrame_clauses» : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$empty_typeFrame:clause:0»  )]


noncomputable def «$empty_typeDefEnv:clause:0»  : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (.bind (.call ⟨(map typeId typeDefIR), SpecTecCall.«$empty_map» typeId typeDefIR⟩) (fun («exec:1» : (map typeId typeDefIR)) => (let «eval:0» : (map typeId typeDefIR) := «exec:1»; (.pure ((«eval:0» : typeDefEnv))))))


noncomputable def «$empty_typeDefEnv_clauses» : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$empty_typeDefEnv:clause:0»  )]


noncomputable def «$empty_callableTypeDefEnv:clause:0»  : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (.bind (.call ⟨(map callableId callableTypeDefIR), SpecTecCall.«$empty_map» callableId callableTypeDefIR⟩) (fun («exec:1» : (map callableId callableTypeDefIR)) => (let «eval:0» : (map callableId callableTypeDefIR) := «exec:1»; (.pure ((«eval:0» : callableTypeDefEnv))))))


noncomputable def «$empty_callableTypeDefEnv_clauses» : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$empty_callableTypeDefEnv:clause:0»  )]


noncomputable def «$empty_constructorTypeDefEnv:clause:0»  : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (.bind (.call ⟨(map constructorId constructorTypeDefIR), SpecTecCall.«$empty_map» constructorId constructorTypeDefIR⟩) (fun («exec:1» : (map constructorId constructorTypeDefIR)) => (let «eval:0» : (map constructorId constructorTypeDefIR) := «exec:1»; (.pure ((«eval:0» : constructorTypeDefEnv))))))


noncomputable def «$empty_constructorTypeDefEnv_clauses» : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$empty_constructorTypeDefEnv:clause:0»  )]


noncomputable def «$empty_typingContext:clause:0»  : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (.bind (.call ⟨constructorTypeDefEnv, SpecTecCall.«$empty_constructorTypeDefEnv»⟩) (fun («exec:1» : constructorTypeDefEnv) => (let «eval:0» : constructorTypeDefEnv := «exec:1»; (.bind (.call ⟨typeDefEnv, SpecTecCall.«$empty_typeDefEnv»⟩) (fun («exec:2» : typeDefEnv) => (let «eval:1» : typeDefEnv := «exec:2»; (.bind (.call ⟨callableTypeDefEnv, SpecTecCall.«$empty_callableTypeDefEnv»⟩) (fun («exec:3» : callableTypeDefEnv) => (let «eval:2» : callableTypeDefEnv := «exec:3»; (.bind (.call ⟨typeFrame, SpecTecCall.«$empty_typeFrame»⟩) (fun («exec:4» : typeFrame) => (let «eval:3» : typeFrame := «exec:4»; (let globalTypingLayer : SpecTec.globalTypingLayer := ({ CONSTRUCTOR := «eval:0», TYPE := «eval:1», CALLABLE := «eval:2», FRAME := «eval:3» } : SpecTec.globalTypingLayer); (.bind (.call ⟨typeDefEnv, SpecTecCall.«$empty_typeDefEnv»⟩) (fun («exec:5» : typeDefEnv) => (let «eval:4» : typeDefEnv := «exec:5»; (.bind (.call ⟨callableTypeDefEnv, SpecTecCall.«$empty_callableTypeDefEnv»⟩) (fun («exec:6» : callableTypeDefEnv) => (let «eval:5» : callableTypeDefEnv := «exec:6»; (.bind (.call ⟨typeFrame, SpecTecCall.«$empty_typeFrame»⟩) (fun («exec:7» : typeFrame) => (let «eval:6» : typeFrame := «exec:7»; (let blockTypingLayer : SpecTec.blockTypingLayer := ({ KIND := ((blockKind._EMPTY) : blockKind), TYPE := «eval:4», CALLABLE := «eval:5», FRAME := «eval:6» } : SpecTec.blockTypingLayer); (.bind (.call ⟨typeDefEnv, SpecTecCall.«$empty_typeDefEnv»⟩) (fun («exec:8» : typeDefEnv) => (let «eval:7» : typeDefEnv := «exec:8»; (.bind (.call ⟨typeFrame, SpecTecCall.«$empty_typeFrame»⟩) (fun («exec:9» : typeFrame) => (let «eval:8» : typeFrame := «exec:9»; (let localTypingLayer : SpecTec.localTypingLayer := ({ KIND := ((localKind._EMPTY) : localKind), TYPE := «eval:7», FRAMES := ([«eval:8»] : (_root_.List typeFrame)) } : SpecTec.localTypingLayer); (let TC : typingContext := ({ CONTROL := ((flow.CONT) : flow), LOOP := ((loop.OUT) : loop), GLOBAL := globalTypingLayer, BLOCK := blockTypingLayer, LOCAL := localTypingLayer } : typingContext); (.pure ((TC : typingContext))))))))))))))))))))))))))))))))))


noncomputable def «$empty_typingContext_clauses» : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$empty_typingContext:clause:0»  )]


noncomputable def «$enter_t:clause:0» (input0 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let TC : typingContext := input0; (.bind (.call ⟨typeFrame, SpecTecCall.«$empty_typeFrame»⟩) (fun («exec:1» : typeFrame) => (let «eval:0» : typeFrame := «exec:1»; (.pure ((({ TC with LOCAL := ({ (typingContext.LOCAL TC) with FRAMES := («eval:0» :: (localTypingLayer.FRAMES (typingContext.LOCAL TC))) } : localTypingLayer) } : typingContext) : typingContext)))))))

end SpecTec
