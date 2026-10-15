import SpecTecDecl0315

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$lift_controlLocalDeclarationIR:clause:1» (input0 : SpecTec.controlLocalDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let controlLocalDeclarationIR : SpecTec.controlLocalDeclarationIR := input0; (.bind (.guard (((«sub:controlLocalDeclarationIR:instantiationIR» controlLocalDeclarationIR) = true))) (fun (_ : Unit) => (match («$lift_controlLocalDeclarationIR:case_2:downcast:0» controlLocalDeclarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.instantiationIR := «exec:1»; (let instantiationIR : SpecTec.instantiationIR := «eval:0»; (.bind (.call ⟨instantiation, SpecTecCall.«$lift_instantiationIR» instantiationIR⟩) (fun («exec:2» : instantiation) => (let «eval:1» : instantiation := «exec:2»; (.pure (((«cast:instantiation:controlLocalDeclaration» «eval:1») : controlLocalDeclaration)))))))) | none => .unmatch))))


noncomputable def «$lift_controlLocalDeclarationIR:clause:2» (input0 : SpecTec.controlLocalDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let controlLocalDeclarationIR : SpecTec.controlLocalDeclarationIR := input0; (.bind (.guard (((«sub:controlLocalDeclarationIR:variableDeclarationIR» controlLocalDeclarationIR) = true))) (fun (_ : Unit) => (match («$lift_controlLocalDeclarationIR:case_3:downcast:0» controlLocalDeclarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.variableDeclarationIR := «exec:1»; (let variableDeclarationIR : SpecTec.variableDeclarationIR := «eval:0»; (.bind (.call ⟨variableDeclaration, SpecTecCall.«$lift_variableDeclarationIR» variableDeclarationIR⟩) (fun («exec:2» : variableDeclaration) => (let «eval:1» : variableDeclaration := «exec:2»; (.pure (((«cast:variableDeclaration:controlLocalDeclaration» «eval:1») : controlLocalDeclaration)))))))) | none => .unmatch))))


noncomputable def «$lift_controlLocalDeclarationIR:clause:3» (input0 : SpecTec.controlLocalDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let controlLocalDeclarationIR : SpecTec.controlLocalDeclarationIR := input0; (.bind (.guard (((«sub:controlLocalDeclarationIR:actionDeclarationIR» controlLocalDeclarationIR) = true))) (fun (_ : Unit) => (match («$lift_controlLocalDeclarationIR:case_4:downcast:0» controlLocalDeclarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.actionDeclarationIR := «exec:1»; (let actionDeclarationIR : SpecTec.actionDeclarationIR := «eval:0»; (.bind (.call ⟨actionDeclaration, SpecTecCall.«$lift_actionDeclarationIR» actionDeclarationIR⟩) (fun («exec:2» : actionDeclaration) => (let «eval:1» : actionDeclaration := «exec:2»; (.pure (((«cast:actionDeclaration:controlLocalDeclaration» «eval:1») : controlLocalDeclaration)))))))) | none => .unmatch))))


noncomputable def «$lift_controlLocalDeclarationIR:clause:4» (input0 : SpecTec.controlLocalDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let controlLocalDeclarationIR : SpecTec.controlLocalDeclarationIR := input0; (.bind (.guard (((«sub:controlLocalDeclarationIR:tableDeclarationIR» controlLocalDeclarationIR) = true))) (fun (_ : Unit) => (match («$lift_controlLocalDeclarationIR:case_5:downcast:0» controlLocalDeclarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.tableDeclarationIR := «exec:1»; (let tableDeclarationIR : SpecTec.tableDeclarationIR := «eval:0»; (.bind (.call ⟨tableDeclaration, SpecTecCall.«$lift_tableDeclarationIR» tableDeclarationIR⟩) (fun («exec:2» : tableDeclaration) => (let «eval:1» : tableDeclaration := «exec:2»; (.pure (((«cast:tableDeclaration:controlLocalDeclaration» «eval:1») : controlLocalDeclaration)))))))) | none => .unmatch))))


noncomputable def «$lift_controlLocalDeclarationIR_clauses» (input0 : controlLocalDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_controlLocalDeclarationIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_controlLocalDeclarationIR:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_controlLocalDeclarationIR:clause:2»  input0), fun (_ : _root_.Unit) => («$lift_controlLocalDeclarationIR:clause:3»  input0), fun (_ : _root_.Unit) => («$lift_controlLocalDeclarationIR:clause:4»  input0)]


noncomputable def «$lift_controlLocalDeclarationListIR:case_1:iter:0:clause:0» (input0 : (_root_.List controlLocalDeclarationIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List controlLocalDeclaration)) : (_root_.List controlLocalDeclaration)))) | _ :: _ => .unmatch)


noncomputable def «$lift_controlLocalDeclarationListIR:case_1:iter:0:clause:1» (input0 : (_root_.List SpecTec.controlLocalDeclarationIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let controlLocalDeclarationIR : SpecTec.controlLocalDeclarationIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.controlLocalDeclarationIR) := «exec:1»; (.bind (.call ⟨SpecTec.controlLocalDeclaration, SpecTecCall.«$lift_controlLocalDeclarationIR» controlLocalDeclarationIR⟩) (fun («exec:3» : SpecTec.controlLocalDeclaration) => (let «eval:1» : SpecTec.controlLocalDeclaration := «exec:3»; (let controlLocalDeclaration : SpecTec.controlLocalDeclaration := «eval:1»; (.bind (.call ⟨(_root_.List SpecTec.controlLocalDeclaration), SpecTecCall.«$lift_controlLocalDeclarationListIR:case_1:iter:0» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.controlLocalDeclaration)) => (let «tail:1» : (_root_.List SpecTec.controlLocalDeclaration) := «exec:4»; (.pure (((controlLocalDeclaration :: «tail:1») : (_root_.List SpecTec.controlLocalDeclaration))))))))))))) | [] => .unmatch)


noncomputable def «$lift_controlLocalDeclarationListIR:case_1:iter:0_clauses» (input0 : (_root_.List controlLocalDeclarationIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_controlLocalDeclarationListIR:case_1:iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_controlLocalDeclarationListIR:case_1:iter:0:clause:1»  input0)]


noncomputable def «$lift_controlLocalDeclarationListIR:clause:0» (input0 : (_root_.List controlLocalDeclarationIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let «controlLocalDeclarationIR*» : (_root_.List controlLocalDeclarationIR) := input0; (.bind (.call ⟨(_root_.List controlLocalDeclaration), SpecTecCall.«$lift_controlLocalDeclarationListIR:case_1:iter:0» «controlLocalDeclarationIR*»⟩) (fun («exec:1» : (_root_.List controlLocalDeclaration)) => (let «controlLocalDeclaration*» : (_root_.List controlLocalDeclaration) := «exec:1»; (.bind (.call ⟨SpecTec.controlLocalDeclarationList, SpecTecCall.«$unflatten_controlLocalDeclarationList» «controlLocalDeclaration*»⟩) (fun («exec:2» : SpecTec.controlLocalDeclarationList) => (let «eval:2» : SpecTec.controlLocalDeclarationList := «exec:2»; (let controlLocalDeclarationList : SpecTec.controlLocalDeclarationList := «eval:2»; (.pure ((controlLocalDeclarationList : SpecTec.controlLocalDeclarationList)))))))))))


noncomputable def «$lift_controlLocalDeclarationListIR_clauses» (input0 : (_root_.List controlLocalDeclarationIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_controlLocalDeclarationListIR:clause:0»  input0)]


noncomputable def «$lift_controlDeclarationIR:clause:0» (input0 : controlDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% CONTROL % `< % ',' % `> `( % `) `( % `) `{ % APPLY % `}» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» «exec:6» «exec:7» «exec:8» => (let annotationList : SpecTec.annotationList := «exec:1»; (let nameIR : SpecTec.nameIR := «exec:2»; (let «typeParameterIR_expl*» : (_root_.List typeParameterIR) := «exec:3»; (let «typeParameterIR_impl*» : (_root_.List typeParameterIR) := «exec:4»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:5»; (let «constructorParameterIR*» : (_root_.List constructorParameterIR) := «exec:6»; (let «controlLocalDeclarationIR*» : (_root_.List controlLocalDeclarationIR) := «exec:7»; (let controlBodyIR : SpecTec.controlBodyIR := «exec:8»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:9» : nonTypeName) => (let «eval:0» : nonTypeName := «exec:9»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:0»); (let «typeParameterIR*» : (_root_.List typeParameterIR) := («typeParameterIR_expl*» ++ «typeParameterIR_impl*»); (.bind (.call ⟨SpecTec.typeParameterListOpt, SpecTecCall.«$lift_typeParameterListIR» «typeParameterIR*»⟩) (fun («exec:10» : SpecTec.typeParameterListOpt) => (let «eval:1» : SpecTec.typeParameterListOpt := «exec:10»; (let typeParameterListOpt : SpecTec.typeParameterListOpt := «eval:1»; (.bind (.call ⟨SpecTec.parameterList, SpecTecCall.«$lift_parameterListIR» «parameterIR*»⟩) (fun («exec:11» : SpecTec.parameterList) => (let «eval:2» : SpecTec.parameterList := «exec:11»; (let parameterList : SpecTec.parameterList := «eval:2»; (.bind (.call ⟨SpecTec.constructorParameterListOpt, SpecTecCall.«$lift_constructorParameterListIR» «constructorParameterIR*»⟩) (fun («exec:12» : SpecTec.constructorParameterListOpt) => (let «eval:3» : SpecTec.constructorParameterListOpt := «exec:12»; (let constructorParameterListOpt : SpecTec.constructorParameterListOpt := «eval:3»; (.bind (.call ⟨SpecTec.controlLocalDeclarationList, SpecTecCall.«$lift_controlLocalDeclarationListIR» «controlLocalDeclarationIR*»⟩) (fun («exec:13» : SpecTec.controlLocalDeclarationList) => (let «eval:4» : SpecTec.controlLocalDeclarationList := «exec:13»; (let controlLocalDeclarationList : SpecTec.controlLocalDeclarationList := «eval:4»; (.bind (.call ⟨SpecTec.controlBody, SpecTecCall.«$lift_controlBodyIR» controlBodyIR⟩) (fun («exec:14» : SpecTec.controlBody) => (let «eval:5» : SpecTec.controlBody := «exec:14»; (let controlBody : SpecTec.controlBody := «eval:5»; (.pure ((((controlDeclaration.«% CONTROL % % `( % `) % `{ % APPLY % `}» annotationList name typeParameterListOpt parameterList constructorParameterListOpt controlLocalDeclarationList controlBody) : controlDeclaration) : controlDeclaration)))))))))))))))))))))))))))))))))))))


noncomputable def «$lift_controlDeclarationIR_clauses» (input0 : controlDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_controlDeclarationIR:clause:0»  input0)]


noncomputable def «$lift_packageTypeDeclarationIR:clause:0» (input0 : packageTypeDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% PACKAGE % `< % ',' % `> `( % `) ';'» «exec:1» «exec:2» «exec:3» «exec:4» «exec:5» => (let annotationList : SpecTec.annotationList := «exec:1»; (let nameIR : SpecTec.nameIR := «exec:2»; (let «typeParameterIR_expl*» : (_root_.List typeParameterIR) := «exec:3»; (let «typeParameterIR_impl*» : (_root_.List typeParameterIR) := «exec:4»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:5»; (.bind (.call ⟨nonTypeName, SpecTecCall.«$lift_nameIR_as_nonTypeName» nameIR⟩) (fun («exec:6» : nonTypeName) => (let «eval:0» : nonTypeName := «exec:6»; (let name : SpecTec.name := («cast:nonTypeName:name» «eval:0»); (let «typeParameterIR*» : (_root_.List typeParameterIR) := («typeParameterIR_expl*» ++ «typeParameterIR_impl*»); (.bind (.call ⟨SpecTec.typeParameterListOpt, SpecTecCall.«$lift_typeParameterListIR» «typeParameterIR*»⟩) (fun («exec:7» : SpecTec.typeParameterListOpt) => (let «eval:1» : SpecTec.typeParameterListOpt := «exec:7»; (let typeParameterListOpt : SpecTec.typeParameterListOpt := «eval:1»; (.bind (.call ⟨SpecTec.parameterList, SpecTecCall.«$lift_parameterListIR» «parameterIR*»⟩) (fun («exec:8» : SpecTec.parameterList) => (let «eval:2» : SpecTec.parameterList := «exec:8»; (let parameterList : SpecTec.parameterList := «eval:2»; (.pure ((((packageTypeDeclaration.«% PACKAGE % % `( % `) ';'» annotationList name typeParameterListOpt parameterList) : packageTypeDeclaration) : packageTypeDeclaration))))))))))))))))))))))


noncomputable def «$lift_packageTypeDeclarationIR_clauses» (input0 : packageTypeDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_packageTypeDeclarationIR:clause:0»  input0)]


noncomputable def «$flatten_typeParameterList:clause:0» (input0 : SpecTec.typeParameterList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeParameterList : SpecTec.typeParameterList := input0; (.bind (.guard (((«sub:typeParameterList:name» typeParameterList) = true))) (fun (_ : Unit) => (match («$flatten_typeParameterList:case_1:downcast:0» typeParameterList) with | some «exec:1» => (let «eval:0» : SpecTec.typeParameter := «exec:1»; (let typeParameter : SpecTec.typeParameter := «eval:0»; (.pure ((([typeParameter] : (_root_.List SpecTec.typeParameter)) : (_root_.List SpecTec.typeParameter)))))) | none => .unmatch))))


noncomputable def «$flatten_typeParameterList:clause:1» (input0 : SpecTec.typeParameterList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeParameterList' : SpecTec.typeParameterList := input0; (.bind (.guard (((«exec:match:typeParameterList:% ',' %» typeParameterList') = true))) (fun (_ : Unit) => (match typeParameterList' with | .«% ',' %» «exec:1» «exec:2» => (let typeParameterList : SpecTec.typeParameterList := «exec:1»; (let typeParameter : SpecTec.typeParameter := «exec:2»; (.bind (.call ⟨(_root_.List SpecTec.typeParameter), SpecTecCall.«$flatten_typeParameterList» typeParameterList⟩) (fun («exec:3» : (_root_.List SpecTec.typeParameter)) => (let «eval:0» : (_root_.List SpecTec.typeParameter) := «exec:3»; (.pure (((«eval:0» ++ ([typeParameter] : (_root_.List SpecTec.typeParameter))) : (_root_.List SpecTec.typeParameter))))))))) | _ => .unmatch))))


noncomputable def «$flatten_typeParameterList_clauses» (input0 : typeParameterList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_typeParameterList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_typeParameterList:clause:1»  input0)]


noncomputable def «$flatten_typeParameterListOpt:clause:0» (input0 : SpecTec.typeParameterListOpt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeParameterListOpt : SpecTec.typeParameterListOpt := input0; (.bind (.guard (((«exec:match:typeParameterListOpt:_EMPTY» typeParameterListOpt) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List typeParameter)) : (_root_.List typeParameter)))))))


noncomputable def «$flatten_typeParameterListOpt:clause:1» (input0 : SpecTec.typeParameterListOpt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeParameterListOpt : SpecTec.typeParameterListOpt := input0; (.bind (.guard (((«exec:match:typeParameterListOpt:`< % `>» typeParameterListOpt) = true))) (fun (_ : Unit) => (match typeParameterListOpt with | .«`< % `>» «exec:1» => (let typeParameterList : SpecTec.typeParameterList := «exec:1»; (.bind (.call ⟨(_root_.List typeParameter), SpecTecCall.«$flatten_typeParameterList» typeParameterList⟩) (fun («exec:2» : (_root_.List typeParameter)) => (let «eval:0» : (_root_.List typeParameter) := «exec:2»; (.pure ((«eval:0» : (_root_.List typeParameter)))))))) | _ => .unmatch))))


noncomputable def «$flatten_typeParameterListOpt_clauses» (input0 : typeParameterListOpt) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_typeParameterListOpt:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_typeParameterListOpt:clause:1»  input0)]


noncomputable def «TypeParameterListOpt_ok:clause:0» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.typeParameterListOpt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC_0 : typingContext := input1; (let typeParameterListOpt : SpecTec.typeParameterListOpt := input2; (.bind (.call ⟨(_root_.List typeParameter), SpecTecCall.«$flatten_typeParameterListOpt» typeParameterListOpt⟩) (fun («exec:1» : (_root_.List typeParameter)) => (let «eval:0» : (_root_.List typeParameter) := «exec:1»; (let «typeParameter*» : (_root_.List typeParameter) := «eval:0»; (.bind (.call ⟨(_root_.List typeId), SpecTecCall.«TypeParameterListOpt_ok:rule:iter:1» «typeParameter*»⟩) (fun («exec:2» : (_root_.List typeId)) => (let «typeId*» : (_root_.List typeId) := «exec:2»; (.bind (.call ⟨typingContext, SpecTecCall.«$add_typeParameters_t» p TC_0 «typeId*»⟩) (fun («exec:3» : typingContext) => (let «eval:3» : typingContext := «exec:3»; (let TC_1 : typingContext := «eval:3»; (.pure (((TC_1, «typeId*») : (typingContext × (_root_.List typeId)))))))))))))))))))


noncomputable def TypeParameterListOpt_ok_clauses (input0 : cursor) (input1 : typingContext) (input2 : typeParameterListOpt) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («TypeParameterListOpt_ok:clause:0»  input0 input1 input2)]


noncomputable def «$lift_typedefIR:clause:0» (input0 : SpecTec.typedefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typedefIR : SpecTec.typedefIR := input0; (.bind (.guard (((«sub:typedefIR:typeIR» typedefIR) = true))) (fun (_ : Unit) => (match («$lift_typedefIR:case_1:downcast:0» typedefIR) with | some «exec:1» => (let «eval:0» : SpecTec.typeIR := «exec:1»; (let typeIR : SpecTec.typeIR := «eval:0»; (.bind (.call ⟨type, SpecTecCall.«$lift_typeIR» typeIR⟩) (fun («exec:2» : type) => (let «eval:1» : type := «exec:2»; (.pure (((«cast:type:typedef» «eval:1») : typedef)))))))) | none => .unmatch))))


noncomputable def «$lift_typedefIR:clause:1» (input0 : SpecTec.typedefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typedefIR : SpecTec.typedefIR := input0; (.bind (.guard (((«sub:typedefIR:derivedTypeDeclarationIR» typedefIR) = true))) (fun (_ : Unit) => (match («$lift_typedefIR:case_2:downcast:0» typedefIR) with | some «exec:1» => (let «eval:0» : SpecTec.derivedTypeDeclarationIR := «exec:1»; (let derivedTypeDeclarationIR : SpecTec.derivedTypeDeclarationIR := «eval:0»; (.bind (.call ⟨derivedTypeDeclaration, SpecTecCall.«$lift_derivedTypeDeclarationIR» derivedTypeDeclarationIR⟩) (fun («exec:2» : derivedTypeDeclaration) => (let «eval:1» : derivedTypeDeclaration := «exec:2»; (.pure (((«cast:derivedTypeDeclaration:typedef» «eval:1») : typedef)))))))) | none => .unmatch))))


noncomputable def «$lift_typedefIR_clauses» (input0 : typedefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_typedefIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_typedefIR:clause:1»  input0)]


noncomputable def «$lift_typedefDeclarationIR:clause:0» (input0 : SpecTec.typedefDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typedefDeclarationIR : SpecTec.typedefDeclarationIR := input0; (.bind (.guard (((«exec:match:typedefDeclarationIR:% TYPEDEF % % ';'» typedefDeclarationIR) = true))) (fun (_ : Unit) => (match typedefDeclarationIR with | .«% TYPEDEF % % ';'» «exec:1» «exec:2» «exec:3» => (let annotationList : SpecTec.annotationList := «exec:1»; (let typedefIR : SpecTec.typedefIR := «exec:2»; (let nameIR : SpecTec.nameIR := «exec:3»; (.bind (.guard (((«sub:typedefIR:typeIR» typedefIR) = true))) (fun (_ : Unit) => (match («$lift_typedefDeclarationIR:case_1:downcast:0» typedefIR) with | some «exec:4» => (let «eval:0» : SpecTec.typeIR := «exec:4»; (let typeIR : SpecTec.typeIR := «eval:0»; (.bind (.call ⟨SpecTec.type, SpecTecCall.«$lift_typeIR» typeIR⟩) (fun («exec:5» : SpecTec.type) => (let «eval:1» : SpecTec.type := «exec:5»; (let type : SpecTec.type := «eval:1»; (.bind (.call ⟨typeName, SpecTecCall.«$lift_nameIR_as_typeName» nameIR⟩) (fun («exec:6» : typeName) => (let «eval:2» : typeName := «exec:6»; (let name : SpecTec.name := («cast:typeIdentifier:name» «eval:2»); (.pure ((((typedefDeclaration.«% TYPEDEF % % ';'» annotationList («cast:type:typedef» type) name) : typedefDeclaration) : typedefDeclaration))))))))))))) | none => .unmatch)))))) | _ => .unmatch))))


noncomputable def «$lift_typedefDeclarationIR:clause:1» (input0 : SpecTec.typedefDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typedefDeclarationIR : SpecTec.typedefDeclarationIR := input0; (.bind (.guard (((«exec:match:typedefDeclarationIR:% TYPEDEF % % ';'» typedefDeclarationIR) = true))) (fun (_ : Unit) => (match typedefDeclarationIR with | .«% TYPEDEF % % ';'» «exec:1» «exec:2» «exec:3» => (let annotationList : SpecTec.annotationList := «exec:1»; (let typedefIR : SpecTec.typedefIR := «exec:2»; (let nameIR : SpecTec.nameIR := «exec:3»; (.bind (.guard (((«sub:typedefIR:derivedTypeDeclarationIR» typedefIR) = true))) (fun (_ : Unit) => (match («$lift_typedefDeclarationIR:case_2:downcast:0» typedefIR) with | some «exec:4» => (let «eval:0» : SpecTec.derivedTypeDeclarationIR := «exec:4»; (let derivedTypeDeclarationIR : SpecTec.derivedTypeDeclarationIR := «eval:0»; (.bind (.call ⟨SpecTec.derivedTypeDeclaration, SpecTecCall.«$lift_derivedTypeDeclarationIR» derivedTypeDeclarationIR⟩) (fun («exec:5» : SpecTec.derivedTypeDeclaration) => (let «eval:1» : SpecTec.derivedTypeDeclaration := «exec:5»; (let derivedTypeDeclaration : SpecTec.derivedTypeDeclaration := «eval:1»; (.bind (.call ⟨typeName, SpecTecCall.«$lift_nameIR_as_typeName» nameIR⟩) (fun («exec:6» : typeName) => (let «eval:2» : typeName := «exec:6»; (let name : SpecTec.name := («cast:typeIdentifier:name» «eval:2»); (.pure ((((typedefDeclaration.«% TYPEDEF % % ';'» annotationList («cast:derivedTypeDeclaration:typedef» derivedTypeDeclaration) name) : typedefDeclaration) : typedefDeclaration))))))))))))) | none => .unmatch)))))) | _ => .unmatch))))


noncomputable def «$lift_typedefDeclarationIR:clause:2» (input0 : SpecTec.typedefDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typedefDeclarationIR : SpecTec.typedefDeclarationIR := input0; (.bind (.guard (((«exec:match:typedefDeclarationIR:% TYPE % % ';'» typedefDeclarationIR) = true))) (fun (_ : Unit) => (match typedefDeclarationIR with | .«% TYPE % % ';'» «exec:1» «exec:2» «exec:3» => (let annotationList : SpecTec.annotationList := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (let nameIR : SpecTec.nameIR := «exec:3»; (.bind (.call ⟨SpecTec.type, SpecTecCall.«$lift_typeIR» typeIR⟩) (fun («exec:4» : SpecTec.type) => (let «eval:0» : SpecTec.type := «exec:4»; (let type : SpecTec.type := «eval:0»; (.bind (.call ⟨typeName, SpecTecCall.«$lift_nameIR_as_typeName» nameIR⟩) (fun («exec:5» : typeName) => (let «eval:1» : typeName := «exec:5»; (let name : SpecTec.name := («cast:typeIdentifier:name» «eval:1»); (.pure ((((typedefDeclaration.«% TYPE % % ';'» annotationList type name) : typedefDeclaration) : typedefDeclaration)))))))))))))) | _ => .unmatch))))


noncomputable def «$lift_typedefDeclarationIR_clauses» (input0 : typedefDeclarationIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$lift_typedefDeclarationIR:clause:0»  input0), fun (_ : _root_.Unit) => («$lift_typedefDeclarationIR:clause:1»  input0), fun (_ : _root_.Unit) => («$lift_typedefDeclarationIR:clause:2»  input0)]


noncomputable def «$lift_typeDeclarationIR:clause:0» (input0 : SpecTec.typeDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDeclarationIR : SpecTec.typeDeclarationIR := input0; (.bind (.guard (((«sub:typeDeclarationIR:derivedTypeDeclarationIR» typeDeclarationIR) = true))) (fun (_ : Unit) => (match («$lift_typeDeclarationIR:case_1:downcast:0» typeDeclarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.derivedTypeDeclarationIR := «exec:1»; (let derivedTypeDeclarationIR : SpecTec.derivedTypeDeclarationIR := «eval:0»; (.bind (.call ⟨derivedTypeDeclaration, SpecTecCall.«$lift_derivedTypeDeclarationIR» derivedTypeDeclarationIR⟩) (fun («exec:2» : derivedTypeDeclaration) => (let «eval:1» : derivedTypeDeclaration := «exec:2»; (.pure (((«cast:derivedTypeDeclaration:typeDeclaration» «eval:1») : typeDeclaration)))))))) | none => .unmatch))))


noncomputable def «$lift_typeDeclarationIR:clause:1» (input0 : SpecTec.typeDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDeclarationIR : SpecTec.typeDeclarationIR := input0; (.bind (.guard (((«sub:typeDeclarationIR:typedefDeclarationIR» typeDeclarationIR) = true))) (fun (_ : Unit) => (match («$lift_typeDeclarationIR:case_2:downcast:0» typeDeclarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.typedefDeclarationIR := «exec:1»; (let typedefDeclarationIR : SpecTec.typedefDeclarationIR := «eval:0»; (.bind (.call ⟨typedefDeclaration, SpecTecCall.«$lift_typedefDeclarationIR» typedefDeclarationIR⟩) (fun («exec:2» : typedefDeclaration) => (let «eval:1» : typedefDeclaration := «exec:2»; (.pure (((«cast:typedefDeclaration:typeDeclaration» «eval:1») : typeDeclaration)))))))) | none => .unmatch))))


noncomputable def «$lift_typeDeclarationIR:clause:2» (input0 : SpecTec.typeDeclarationIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeDeclarationIR : SpecTec.typeDeclarationIR := input0; (.bind (.guard (((«sub:typeDeclarationIR:parserTypeDeclarationIR» typeDeclarationIR) = true))) (fun (_ : Unit) => (match («$lift_typeDeclarationIR:case_3:downcast:0» typeDeclarationIR) with | some «exec:1» => (let «eval:0» : SpecTec.parserTypeDeclarationIR := «exec:1»; (let parserTypeDeclarationIR : SpecTec.parserTypeDeclarationIR := «eval:0»; (.bind (.call ⟨parserTypeDeclaration, SpecTecCall.«$lift_parserTypeDeclarationIR» parserTypeDeclarationIR⟩) (fun («exec:2» : parserTypeDeclaration) => (let «eval:1» : parserTypeDeclaration := «exec:2»; (.pure (((«cast:parserTypeDeclaration:typeDeclaration» «eval:1») : typeDeclaration)))))))) | none => .unmatch))))

end SpecTec
