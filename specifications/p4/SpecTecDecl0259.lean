import SpecTecDecl0258

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$is_externConstructorPrototype:clause:1» (input0 : SpecTec.externConstructorOrMethodPrototype) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externConstructorOrMethodPrototype : SpecTec.externConstructorOrMethodPrototype := input0; (.pure ((false : _root_.Bool))))


noncomputable def «$is_externConstructorPrototype_clauses» (input0 : externConstructorOrMethodPrototype) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_externConstructorPrototype:clause:0»  input0), fun (_ : _root_.Unit) => («$is_externConstructorPrototype:clause:1»  input0)]


noncomputable def «$is_externMethodPrototype:clause:0» (input0 : SpecTec.externConstructorOrMethodPrototype) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externConstructorOrMethodPrototype : SpecTec.externConstructorOrMethodPrototype := input0; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_externConstructorPrototype» externConstructorOrMethodPrototype⟩) (fun («exec:1» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:1»; (.pure (((!«eval:0») : _root_.Bool)))))))


noncomputable def «$is_externMethodPrototype_clauses» (input0 : externConstructorOrMethodPrototype) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_externMethodPrototype:clause:0»  input0)]


noncomputable def «$split_externConstructorOrMethodPrototypeList:case_1:iter:1:clause:0» (input0 : (_root_.List externConstructorOrMethodPrototype)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$split_externConstructorOrMethodPrototypeList:case_1:iter:1:clause:1» (input0 : (_root_.List SpecTec.externConstructorOrMethodPrototype)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let externConstructorOrMethodPrototype : SpecTec.externConstructorOrMethodPrototype := «exec:2»; (let «tail:0» : (_root_.List SpecTec.externConstructorOrMethodPrototype) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_externConstructorPrototype» externConstructorOrMethodPrototype⟩) (fun («exec:3» : _root_.Bool) => (let «eval:2» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$split_externConstructorOrMethodPrototypeList:case_1:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:2» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «$split_externConstructorOrMethodPrototypeList:case_1:iter:1_clauses» (input0 : (_root_.List externConstructorOrMethodPrototype)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$split_externConstructorOrMethodPrototypeList:case_1:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$split_externConstructorOrMethodPrototypeList:case_1:iter:1:clause:1»  input0)]


noncomputable def «$split_externConstructorOrMethodPrototypeList:case_1:iter:6:clause:0» (input0 : (_root_.List externConstructorOrMethodPrototype)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «$split_externConstructorOrMethodPrototypeList:case_1:iter:6:clause:1» (input0 : (_root_.List SpecTec.externConstructorOrMethodPrototype)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let externConstructorOrMethodPrototype : SpecTec.externConstructorOrMethodPrototype := «exec:2»; (let «tail:0» : (_root_.List SpecTec.externConstructorOrMethodPrototype) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_externMethodPrototype» externConstructorOrMethodPrototype⟩) (fun («exec:3» : _root_.Bool) => (let «eval:7» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$split_externConstructorOrMethodPrototypeList:case_1:iter:6» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:7» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «$split_externConstructorOrMethodPrototypeList:case_1:iter:6_clauses» (input0 : (_root_.List externConstructorOrMethodPrototype)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$split_externConstructorOrMethodPrototypeList:case_1:iter:6:clause:0»  input0), fun (_ : _root_.Unit) => («$split_externConstructorOrMethodPrototypeList:case_1:iter:6:clause:1»  input0)]


noncomputable def «$split_externConstructorOrMethodPrototypeList:clause:0» (input0 : SpecTec.externConstructorOrMethodPrototypeList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let externConstructorOrMethodPrototypeList : SpecTec.externConstructorOrMethodPrototypeList := input0; (.bind (.call ⟨(_root_.List externConstructorOrMethodPrototype), SpecTecCall.«$flatten_externConstructorOrMethodPrototypeList» externConstructorOrMethodPrototypeList⟩) (fun («exec:1» : (_root_.List externConstructorOrMethodPrototype)) => (let «eval:0» : (_root_.List externConstructorOrMethodPrototype) := «exec:1»; (let «externConstructorOrMethodPrototype*» : (_root_.List externConstructorOrMethodPrototype) := «eval:0»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$split_externConstructorOrMethodPrototypeList:case_1:iter:1» «externConstructorOrMethodPrototype*»⟩) (fun («exec:2» : (_root_.List _root_.Bool)) => (let «eval:3» : (_root_.List _root_.Bool) := «exec:2»; (.bind (.call ⟨(_root_.List externConstructorOrMethodPrototype), SpecTecCall.«$filter_» externConstructorOrMethodPrototype «externConstructorOrMethodPrototype*» «eval:3»⟩) (fun («exec:3» : (_root_.List externConstructorOrMethodPrototype)) => (let «eval:4» : (_root_.List externConstructorOrMethodPrototype) := «exec:3»; (let «externConstructorOrMethodPrototype'*» : (_root_.List externConstructorOrMethodPrototype) := «eval:4»; (.bind (.guard (((_root_.List.all «externConstructorOrMethodPrototype'*» (fun («sub:item» : externConstructorOrMethodPrototype) => («sub:externConstructorOrMethodPrototype:externConstructorPrototype» «sub:item»))) = true))) (fun (_ : Unit) => (match (_root_.List.mapM (fun («$split_externConstructorOrMethodPrototypeList:case_1:downcast:5:item» : externConstructorOrMethodPrototype) => («$split_externConstructorOrMethodPrototypeList:case_1:downcast:5:0» «$split_externConstructorOrMethodPrototypeList:case_1:downcast:5:item»)) «externConstructorOrMethodPrototype'*») with | some «exec:4» => (let «eval:5» : (_root_.List externConstructorPrototype) := «exec:4»; (let «externConstructorPrototype*» : (_root_.List externConstructorPrototype) := «eval:5»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«$split_externConstructorOrMethodPrototypeList:case_1:iter:6» «externConstructorOrMethodPrototype*»⟩) (fun («exec:5» : (_root_.List _root_.Bool)) => (let «eval:8» : (_root_.List _root_.Bool) := «exec:5»; (.bind (.call ⟨(_root_.List externConstructorOrMethodPrototype), SpecTecCall.«$filter_» externConstructorOrMethodPrototype «externConstructorOrMethodPrototype*» «eval:8»⟩) (fun («exec:6» : (_root_.List externConstructorOrMethodPrototype)) => (let «eval:9» : (_root_.List externConstructorOrMethodPrototype) := «exec:6»; (let «externConstructorOrMethodPrototype''*» : (_root_.List externConstructorOrMethodPrototype) := «eval:9»; (.bind (.guard (((_root_.List.all «externConstructorOrMethodPrototype''*» (fun («sub:item» : externConstructorOrMethodPrototype) => («sub:externConstructorOrMethodPrototype:externMethodPrototype» «sub:item»))) = true))) (fun (_ : Unit) => (match (_root_.List.mapM (fun («$split_externConstructorOrMethodPrototypeList:case_1:downcast:10:item» : externConstructorOrMethodPrototype) => («$split_externConstructorOrMethodPrototypeList:case_1:downcast:10:0» «$split_externConstructorOrMethodPrototypeList:case_1:downcast:10:item»)) «externConstructorOrMethodPrototype''*») with | some «exec:7» => (let «eval:10» : (_root_.List externMethodPrototype) := «exec:7»; (let «externMethodPrototype*» : (_root_.List externMethodPrototype) := «eval:10»; (.pure (((«externConstructorPrototype*», «externMethodPrototype*») : ((_root_.List externConstructorPrototype) × (_root_.List externMethodPrototype))))))) | none => .unmatch)))))))))))) | none => .unmatch)))))))))))))))


noncomputable def «$split_externConstructorOrMethodPrototypeList_clauses» (input0 : externConstructorOrMethodPrototypeList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$split_externConstructorOrMethodPrototypeList:clause:0»  input0)]


noncomputable def «$flatten_forInitStatementList:clause:0» (input0 : SpecTec.forInitStatementList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let forInitStatementList : SpecTec.forInitStatementList := input0; (.bind (.guard (((«exec:match:forInitStatementList:_EMPTY» forInitStatementList) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List forInitStatement)) : (_root_.List forInitStatement)))))))


noncomputable def «$flatten_forInitStatementList:clause:1» (input0 : SpecTec.forInitStatementList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let forInitStatementList : SpecTec.forInitStatementList := input0; (.bind (.guard (((«sub:forInitStatementList:forInitStatement» forInitStatementList) = true))) (fun (_ : Unit) => (match («$flatten_forInitStatementList:case_2:downcast:0» forInitStatementList) with | some «exec:1» => (let «eval:0» : SpecTec.forInitStatement := «exec:1»; (let forInitStatement : SpecTec.forInitStatement := «eval:0»; (.pure ((([forInitStatement] : (_root_.List SpecTec.forInitStatement)) : (_root_.List SpecTec.forInitStatement)))))) | none => .unmatch))))


noncomputable def «$flatten_forInitStatementList:clause:2» (input0 : SpecTec.forInitStatementList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let forInitStatementList : SpecTec.forInitStatementList := input0; (.bind (.guard (((«sub:forInitStatementList:forInitStatementListNonEmpty» forInitStatementList) = true))) (fun (_ : Unit) => (match («$flatten_forInitStatementList:case_3:downcast:0» forInitStatementList) with | some «exec:1» => (let «eval:0» : SpecTec.forInitStatementListNonEmpty := «exec:1»; (let forInitStatementListNonEmpty' : SpecTec.forInitStatementListNonEmpty := «eval:0»; (.bind (.guard (((«exec:match:forInitStatementListNonEmpty:% ',' %» forInitStatementListNonEmpty') = true))) (fun (_ : Unit) => (match forInitStatementListNonEmpty' with | .«% ',' %» «exec:2» «exec:3» => (let forInitStatementListNonEmpty : SpecTec.forInitStatementListNonEmpty := «exec:2»; (let forInitStatement : SpecTec.forInitStatement := «exec:3»; (.bind (.call ⟨(_root_.List SpecTec.forInitStatement), SpecTecCall.«$flatten_forInitStatementList» («cast:forInitStatementListNonEmpty:forInitStatementList» forInitStatementListNonEmpty)⟩) (fun («exec:4» : (_root_.List SpecTec.forInitStatement)) => (let «eval:1» : (_root_.List SpecTec.forInitStatement) := «exec:4»; (.pure (((«eval:1» ++ ([forInitStatement] : (_root_.List SpecTec.forInitStatement))) : (_root_.List SpecTec.forInitStatement))))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$flatten_forInitStatementList_clauses» (input0 : forInitStatementList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_forInitStatementList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_forInitStatementList:clause:1»  input0), fun (_ : _root_.Unit) => («$flatten_forInitStatementList:clause:2»  input0)]


noncomputable def «$flatten_forUpdateStatementList:clause:0» (input0 : SpecTec.forUpdateStatementList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let forUpdateStatementList : SpecTec.forUpdateStatementList := input0; (.bind (.guard (((«exec:match:forUpdateStatementList:_EMPTY» forUpdateStatementList) = true))) (fun (_ : Unit) => (.pure ((([] : (_root_.List forUpdateStatement)) : (_root_.List forUpdateStatement)))))))


noncomputable def «$flatten_forUpdateStatementList:clause:1» (input0 : SpecTec.forUpdateStatementList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let forUpdateStatementList : SpecTec.forUpdateStatementList := input0; (.bind (.guard (((«sub:forUpdateStatementList:forUpdateStatement» forUpdateStatementList) = true))) (fun (_ : Unit) => (match («$flatten_forUpdateStatementList:case_2:downcast:0» forUpdateStatementList) with | some «exec:1» => (let «eval:0» : SpecTec.forUpdateStatement := «exec:1»; (let forUpdateStatement : SpecTec.forUpdateStatement := «eval:0»; (.pure ((([forUpdateStatement] : (_root_.List SpecTec.forUpdateStatement)) : (_root_.List SpecTec.forUpdateStatement)))))) | none => .unmatch))))


noncomputable def «$flatten_forUpdateStatementList:clause:2» (input0 : SpecTec.forUpdateStatementList) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let forUpdateStatementList : SpecTec.forUpdateStatementList := input0; (.bind (.guard (((«sub:forUpdateStatementList:forUpdateStatementListNonEmpty» forUpdateStatementList) = true))) (fun (_ : Unit) => (match («$flatten_forUpdateStatementList:case_3:downcast:0» forUpdateStatementList) with | some «exec:1» => (let «eval:0» : SpecTec.forUpdateStatementListNonEmpty := «exec:1»; (let forUpdateStatementListNonEmpty' : SpecTec.forUpdateStatementListNonEmpty := «eval:0»; (.bind (.guard (((«exec:match:forUpdateStatementListNonEmpty:% ',' %» forUpdateStatementListNonEmpty') = true))) (fun (_ : Unit) => (match forUpdateStatementListNonEmpty' with | .«% ',' %» «exec:2» «exec:3» => (let forUpdateStatementListNonEmpty : SpecTec.forUpdateStatementListNonEmpty := «exec:2»; (let forUpdateStatement : SpecTec.forUpdateStatement := «exec:3»; (.bind (.call ⟨(_root_.List SpecTec.forUpdateStatement), SpecTecCall.«$flatten_forUpdateStatementList» («cast:forUpdateStatementListNonEmpty:forUpdateStatementList» forUpdateStatementListNonEmpty)⟩) (fun («exec:4» : (_root_.List SpecTec.forUpdateStatement)) => (let «eval:1» : (_root_.List SpecTec.forUpdateStatement) := «exec:4»; (.pure (((«eval:1» ++ ([forUpdateStatement] : (_root_.List SpecTec.forUpdateStatement))) : (_root_.List SpecTec.forUpdateStatement))))))))) | _ => .unmatch))))) | none => .unmatch))))


noncomputable def «$flatten_forUpdateStatementList_clauses» (input0 : forUpdateStatementList) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$flatten_forUpdateStatementList:clause:0»  input0), fun (_ : _root_.Unit) => («$flatten_forUpdateStatementList:clause:1»  input0), fun (_ : _root_.Unit) => («$flatten_forUpdateStatementList:clause:2»  input0)]


noncomputable def «$parameterListIR_of_functionDef:clause:0» (input0 : SpecTec.functionDef) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let functionDef : SpecTec.functionDef := input0; (.bind (.guard (((«sub:functionDef:definedFunctionDef» functionDef) = true))) (fun (_ : Unit) => (match («$parameterListIR_of_functionDef:case_1:downcast:0» functionDef) with | some «exec:1» => (let «eval:0» : SpecTec.definedFunctionDef := «exec:1»; (let definedFunctionDef : SpecTec.definedFunctionDef := «eval:0»; (.bind (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_definedFunctionDef» definedFunctionDef⟩) (fun («exec:2» : (_root_.List parameterIR)) => (let «eval:1» : (_root_.List parameterIR) := «exec:2»; (.pure ((«eval:1» : (_root_.List parameterIR))))))))) | none => .unmatch))))


noncomputable def «$parameterListIR_of_functionDef:clause:1» (input0 : SpecTec.functionDef) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let functionDef : SpecTec.functionDef := input0; (.bind (.guard (((«sub:functionDef:externFunctionDef» functionDef) = true))) (fun (_ : Unit) => (match («$parameterListIR_of_functionDef:case_2:downcast:0» functionDef) with | some «exec:1» => (let «eval:0» : SpecTec.externFunctionDef := «exec:1»; (let externFunctionDef : SpecTec.externFunctionDef := «eval:0»; (.bind (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_externFunctionDef» externFunctionDef⟩) (fun («exec:2» : (_root_.List parameterIR)) => (let «eval:1» : (_root_.List parameterIR) := «exec:2»; (.pure ((«eval:1» : (_root_.List parameterIR))))))))) | none => .unmatch))))


noncomputable def «$parameterListIR_of_functionDef_clauses» (input0 : functionDef) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$parameterListIR_of_functionDef:clause:0»  input0), fun (_ : _root_.Unit) => («$parameterListIR_of_functionDef:clause:1»  input0)]


noncomputable def «$parameterListIR_of_functionTypeDefIR:clause:0» (input0 : SpecTec.functionTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let functionTypeDefIR : SpecTec.functionTypeDefIR := input0; (.bind (.guard (((«sub:functionTypeDefIR:definedFunctionTypeDefIR» functionTypeDefIR) = true))) (fun (_ : Unit) => (match («$parameterListIR_of_functionTypeDefIR:case_1:downcast:0» functionTypeDefIR) with | some «exec:1» => (let «eval:0» : SpecTec.definedFunctionTypeDefIR := «exec:1»; (let definedFunctionTypeDefIR : SpecTec.definedFunctionTypeDefIR := «eval:0»; (.bind (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_definedFunctionTypeDefIR» definedFunctionTypeDefIR⟩) (fun («exec:2» : (_root_.List parameterIR)) => (let «eval:1» : (_root_.List parameterIR) := «exec:2»; (.pure ((«eval:1» : (_root_.List parameterIR))))))))) | none => .unmatch))))


noncomputable def «$parameterListIR_of_functionTypeDefIR:clause:1» (input0 : SpecTec.functionTypeDefIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let functionTypeDefIR : SpecTec.functionTypeDefIR := input0; (.bind (.guard (((«sub:functionTypeDefIR:externFunctionTypeDefIR» functionTypeDefIR) = true))) (fun (_ : Unit) => (match («$parameterListIR_of_functionTypeDefIR:case_2:downcast:0» functionTypeDefIR) with | some «exec:1» => (let «eval:0» : SpecTec.externFunctionTypeDefIR := «exec:1»; (let externFunctionTypeDefIR : SpecTec.externFunctionTypeDefIR := «eval:0»; (.bind (.call ⟨(_root_.List parameterIR), SpecTecCall.«$parameterListIR_of_externFunctionTypeDefIR» externFunctionTypeDefIR⟩) (fun («exec:2» : (_root_.List parameterIR)) => (let «eval:1» : (_root_.List parameterIR) := «exec:2»; (.pure ((«eval:1» : (_root_.List parameterIR))))))))) | none => .unmatch))))


noncomputable def «$parameterListIR_of_functionTypeDefIR_clauses» (input0 : functionTypeDefIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$parameterListIR_of_functionTypeDefIR:clause:0»  input0), fun (_ : _root_.Unit) => («$parameterListIR_of_functionTypeDefIR:clause:1»  input0)]


noncomputable def «$width_of_integerTypeIR:clause:0» (input0 : SpecTec.integerTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let integerTypeIR : SpecTec.integerTypeIR := input0; (.bind (.guard (((«sub:integerTypeIR:intTypeIR» integerTypeIR) = true))) (fun (_ : Unit) => (match («$width_of_integerTypeIR:case_1:downcast:0» integerTypeIR) with | some «exec:1» => (let «eval:0» : SpecTec.intTypeIR := «exec:1»; (let intTypeIR : SpecTec.intTypeIR := «eval:0»; (.bind (.guard (((SpecTec.intTypeIR.INT) : SpecTec.intTypeIR) = intTypeIR)) (fun (_ : Unit) => (.pure ((((_root_.Option.none) : (_root_.Option _root_.Nat)) : (_root_.Option _root_.Nat)))))))) | none => .unmatch))))


noncomputable def «$width_of_integerTypeIR:clause:1» (input0 : SpecTec.integerTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let integerTypeIR : SpecTec.integerTypeIR := input0; (.bind (.guard (((«sub:integerTypeIR:fixedIntTypeIR» integerTypeIR) = true))) (fun (_ : Unit) => (match («$width_of_integerTypeIR:case_2:downcast:0» integerTypeIR) with | some «exec:1» => (let «eval:0» : fixedIntTypeIR := «exec:1»; (match «eval:0» with | .«INT `< % `>» «exec:2» => (let n : _root_.Nat := «exec:2»; (.pure (((_root_.Option.some n) : (_root_.Option _root_.Nat))))))) | none => .unmatch))))


noncomputable def «$width_of_integerTypeIR:clause:2» (input0 : SpecTec.integerTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let integerTypeIR : SpecTec.integerTypeIR := input0; (.bind (.guard (((«sub:integerTypeIR:fixedBitTypeIR» integerTypeIR) = true))) (fun (_ : Unit) => (match («$width_of_integerTypeIR:case_3:downcast:0» integerTypeIR) with | some «exec:1» => (let «eval:0» : fixedBitTypeIR := «exec:1»; (match «eval:0» with | .«BIT `< % `>» «exec:2» => (let n : _root_.Nat := «exec:2»; (.pure (((_root_.Option.some n) : (_root_.Option _root_.Nat))))))) | none => .unmatch))))


noncomputable def «$width_of_integerTypeIR:clause:3» (input0 : SpecTec.integerTypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let integerTypeIR : SpecTec.integerTypeIR := input0; (.bind (.guard (((«sub:integerTypeIR:varBitTypeIR» integerTypeIR) = true))) (fun (_ : Unit) => (match («$width_of_integerTypeIR:case_4:downcast:0» integerTypeIR) with | some «exec:1» => (let «eval:0» : varBitTypeIR := «exec:1»; (match «eval:0» with | .«VARBIT `< % `>» «exec:2» => (let n : _root_.Nat := «exec:2»; (.pure (((_root_.Option.some n) : (_root_.Option _root_.Nat))))))) | none => .unmatch))))


noncomputable def «$width_of_integerTypeIR_clauses» (input0 : integerTypeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$width_of_integerTypeIR:clause:0»  input0), fun (_ : _root_.Unit) => («$width_of_integerTypeIR:clause:1»  input0), fun (_ : _root_.Unit) => («$width_of_integerTypeIR:clause:2»  input0), fun (_ : _root_.Unit) => («$width_of_integerTypeIR:clause:3»  input0)]


noncomputable def «$int_of_integerValue:clause:0» (input0 : SpecTec.integerValue) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let integerValue : SpecTec.integerValue := input0; (.bind (.guard (((«sub:integerValue:integerLiteral» integerValue) = true))) (fun (_ : Unit) => (match («$int_of_integerValue:case_1:downcast:0» integerValue) with | some «exec:1» => (let «eval:0» : SpecTec.integerLiteral := «exec:1»; (let integerLiteral : SpecTec.integerLiteral := «eval:0»; (.bind (.guard (((«exec:match:integerLiteral:D» integerLiteral) = true))) (fun (_ : Unit) => (match integerLiteral with | .D «exec:2» => (let i : _root_.Int := «exec:2»; (.pure ((i : _root_.Int)))) | _ => .unmatch))))) | none => .unmatch))))

end SpecTec
