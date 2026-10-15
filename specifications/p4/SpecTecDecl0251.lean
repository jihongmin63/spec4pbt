import SpecTecDecl0250

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$text_of_number_tableKeyValueInterface:clause:0» (input0 : SpecTec.tableKeyValueInterface) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableKeyValueInterface : SpecTec.tableKeyValueInterface := input0; (.bind (.guard (((«exec:match:tableKeyValueInterface:_BIN» tableKeyValueInterface) = true))) (fun (_ : Unit) => (match tableKeyValueInterface with | ._BIN «exec:1» => (let t : _root_.String := «exec:1»; (.pure (((_root_.Option.some ("0b" ++ t)) : (_root_.Option _root_.String))))) | _ => .unmatch))))


noncomputable def «$text_of_number_tableKeyValueInterface:clause:1» (input0 : SpecTec.tableKeyValueInterface) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableKeyValueInterface : SpecTec.tableKeyValueInterface := input0; (.bind (.guard (((«exec:match:tableKeyValueInterface:_HEX» tableKeyValueInterface) = true))) (fun (_ : Unit) => (match tableKeyValueInterface with | ._HEX «exec:1» => (let t : _root_.String := «exec:1»; (.pure (((_root_.Option.some ("0x" ++ t)) : (_root_.Option _root_.String))))) | _ => .unmatch))))


noncomputable def «$text_of_number_tableKeyValueInterface:clause:2» (input0 : SpecTec.tableKeyValueInterface) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableKeyValueInterface : SpecTec.tableKeyValueInterface := input0; (.bind (.guard (((«exec:match:tableKeyValueInterface:_DEC» tableKeyValueInterface) = true))) (fun (_ : Unit) => (match tableKeyValueInterface with | ._DEC «exec:1» => (let t : _root_.String := «exec:1»; (.pure (((_root_.Option.some t) : (_root_.Option _root_.String))))) | _ => .unmatch))))


noncomputable def «$text_of_number_tableKeyValueInterface:clause:3» (input0 : SpecTec.tableKeyValueInterface) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableKeyValueInterface : SpecTec.tableKeyValueInterface := input0; (.bind (.guard (((«exec:match:tableKeyValueInterface:% _SLASH %» tableKeyValueInterface) = true))) (fun (_ : Unit) => (match tableKeyValueInterface with | .«% _SLASH %» «exec:1» «exec:2» => (let _t : _root_.String := «exec:1»; (let _nat : _root_.Nat := «exec:2»; (.pure ((((_root_.Option.none) : (_root_.Option _root_.String)) : (_root_.Option _root_.String)))))) | _ => .unmatch))))


noncomputable def «$text_of_number_tableKeyValueInterface_clauses» (input0 : tableKeyValueInterface) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$text_of_number_tableKeyValueInterface:clause:0»  input0), fun (_ : _root_.Unit) => («$text_of_number_tableKeyValueInterface:clause:1»  input0), fun (_ : _root_.Unit) => («$text_of_number_tableKeyValueInterface:clause:2»  input0), fun (_ : _root_.Unit) => («$text_of_number_tableKeyValueInterface:clause:3»  input0)]


noncomputable def «$is_tableDefaultActionProperty:clause:0» (input0 : SpecTec.tableProperty) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableProperty : SpecTec.tableProperty := input0; (.bind (.guard (((«exec:match:tableProperty:% % % % ';'» tableProperty) = true))) (fun (_ : Unit) => (match tableProperty with | .«% % % % ';'» «exec:1» «exec:2» «exec:3» «exec:4» => (let _annotationList : annotationList := «exec:1»; (let _constOpt : constOpt := «exec:2»; (let tableCustomName : SpecTec.tableCustomName := «exec:3»; (let _initializer : initializer := «exec:4»; (.bind (.call ⟨nameIR, SpecTecCall.«$tableCustomName» tableCustomName⟩) (fun («exec:5» : nameIR) => (let «eval:0» : nameIR := «exec:5»; (.bind (.guard («eval:0» = "default_action")) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))))))))) | _ => .unmatch))))


noncomputable def «$is_tableDefaultActionProperty:clause:1» (input0 : tableProperty) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _tableProperty : tableProperty := input0; (.pure ((false : _root_.Bool))))


noncomputable def «$is_tableDefaultActionProperty_clauses» (input0 : tableProperty) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_tableDefaultActionProperty:clause:0»  input0), fun (_ : _root_.Unit) => («$is_tableDefaultActionProperty:clause:1»  input0)]


noncomputable def «Table_ok:zero-default-action:iter:8:clause:0» (input0 : (_root_.List tableProperty)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «Table_ok:zero-default-action:iter:8:clause:1» (input0 : (_root_.List SpecTec.tableProperty)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableProperty : SpecTec.tableProperty := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableProperty) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_tableDefaultActionProperty» tableProperty⟩) (fun («exec:3» : _root_.Bool) => (let «eval:9» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Table_ok:zero-default-action:iter:8» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:9» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «Table_ok:zero-default-action:iter:8_clauses» (input0 : (_root_.List tableProperty)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Table_ok:zero-default-action:iter:8:clause:0»  input0), fun (_ : _root_.Unit) => («Table_ok:zero-default-action:iter:8:clause:1»  input0)]


noncomputable def «Table_ok:one-default-action:iter:8:clause:0» (input0 : (_root_.List tableProperty)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «Table_ok:one-default-action:iter:8:clause:1» (input0 : (_root_.List SpecTec.tableProperty)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableProperty : SpecTec.tableProperty := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableProperty) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_tableDefaultActionProperty» tableProperty⟩) (fun («exec:3» : _root_.Bool) => (let «eval:9» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Table_ok:one-default-action:iter:8» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:9» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «Table_ok:one-default-action:iter:8_clauses» (input0 : (_root_.List tableProperty)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Table_ok:one-default-action:iter:8:clause:0»  input0), fun (_ : _root_.Unit) => («Table_ok:one-default-action:iter:8:clause:1»  input0)]


noncomputable def «$is_tableLargestPriorityWinsProperty:clause:0» (input0 : SpecTec.tableProperty) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableProperty : SpecTec.tableProperty := input0; (.bind (.guard (((«exec:match:tableProperty:% % % % ';'» tableProperty) = true))) (fun (_ : Unit) => (match tableProperty with | .«% % % % ';'» «exec:1» «exec:2» «exec:3» «exec:4» => (let _annotationList : annotationList := «exec:1»; (let _constOpt : constOpt := «exec:2»; (let tableCustomName : SpecTec.tableCustomName := «exec:3»; (let _initializer : initializer := «exec:4»; (.bind (.call ⟨nameIR, SpecTecCall.«$tableCustomName» tableCustomName⟩) (fun («exec:5» : nameIR) => (let «eval:0» : nameIR := «exec:5»; (.bind (.guard («eval:0» = "largest_priority_wins")) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))))))))) | _ => .unmatch))))


noncomputable def «$is_tableLargestPriorityWinsProperty:clause:1» (input0 : tableProperty) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _tableProperty : tableProperty := input0; (.pure ((false : _root_.Bool))))


noncomputable def «$is_tableLargestPriorityWinsProperty_clauses» (input0 : tableProperty) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_tableLargestPriorityWinsProperty:clause:0»  input0), fun (_ : _root_.Unit) => («$is_tableLargestPriorityWinsProperty:clause:1»  input0)]


noncomputable def «Table_ok:zero-default-action:iter:12:clause:0» (input0 : (_root_.List tableProperty)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «Table_ok:zero-default-action:iter:12:clause:1» (input0 : (_root_.List SpecTec.tableProperty)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableProperty : SpecTec.tableProperty := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableProperty) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_tableLargestPriorityWinsProperty» tableProperty⟩) (fun («exec:3» : _root_.Bool) => (let «eval:13» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Table_ok:zero-default-action:iter:12» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:13» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «Table_ok:zero-default-action:iter:12_clauses» (input0 : (_root_.List tableProperty)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Table_ok:zero-default-action:iter:12:clause:0»  input0), fun (_ : _root_.Unit) => («Table_ok:zero-default-action:iter:12:clause:1»  input0)]


noncomputable def «Table_ok:one-default-action:iter:12:clause:0» (input0 : (_root_.List tableProperty)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «Table_ok:one-default-action:iter:12:clause:1» (input0 : (_root_.List SpecTec.tableProperty)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableProperty : SpecTec.tableProperty := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableProperty) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_tableLargestPriorityWinsProperty» tableProperty⟩) (fun («exec:3» : _root_.Bool) => (let «eval:13» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Table_ok:one-default-action:iter:12» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:13» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «Table_ok:one-default-action:iter:12_clauses» (input0 : (_root_.List tableProperty)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Table_ok:one-default-action:iter:12:clause:0»  input0), fun (_ : _root_.Unit) => («Table_ok:one-default-action:iter:12:clause:1»  input0)]


noncomputable def «$is_tableActionsProperty:clause:0» (input0 : SpecTec.tableProperty) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tableProperty : SpecTec.tableProperty := input0; (.bind (.guard (((«exec:match:tableProperty:ACTIONS '=' `{ % `}» tableProperty) = true))) (fun (_ : Unit) => (match tableProperty with | .«ACTIONS '=' `{ % `}» «exec:1» => (let _tableActionList : tableActionList := «exec:1»; (.pure ((true : _root_.Bool)))) | _ => .unmatch))))


noncomputable def «$is_tableActionsProperty:clause:1» (input0 : tableProperty) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _tableProperty : tableProperty := input0; (.pure ((false : _root_.Bool))))


noncomputable def «$is_tableActionsProperty_clauses» (input0 : tableProperty) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$is_tableActionsProperty:clause:0»  input0), fun (_ : _root_.Unit) => («$is_tableActionsProperty:clause:1»  input0)]


noncomputable def «Table_ok:zero-default-action:iter:4:clause:0» (input0 : (_root_.List tableProperty)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «Table_ok:zero-default-action:iter:4:clause:1» (input0 : (_root_.List SpecTec.tableProperty)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableProperty : SpecTec.tableProperty := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableProperty) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_tableActionsProperty» tableProperty⟩) (fun («exec:3» : _root_.Bool) => (let «eval:5» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Table_ok:zero-default-action:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:5» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «Table_ok:zero-default-action:iter:4_clauses» (input0 : (_root_.List tableProperty)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Table_ok:zero-default-action:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Table_ok:zero-default-action:iter:4:clause:1»  input0)]


noncomputable def «Table_ok:one-default-action:iter:4:clause:0» (input0 : (_root_.List tableProperty)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Bool)) : (_root_.List _root_.Bool)))) | _ :: _ => .unmatch)


noncomputable def «Table_ok:one-default-action:iter:4:clause:1» (input0 : (_root_.List SpecTec.tableProperty)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let tableProperty : SpecTec.tableProperty := «exec:2»; (let «tail:0» : (_root_.List SpecTec.tableProperty) := «exec:1»; (.bind (.call ⟨_root_.Bool, SpecTecCall.«$is_tableActionsProperty» tableProperty⟩) (fun («exec:3» : _root_.Bool) => (let «eval:5» : _root_.Bool := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Bool), SpecTecCall.«Table_ok:one-default-action:iter:4» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Bool)) => (let «tail:1» : (_root_.List _root_.Bool) := «exec:4»; (.pure (((«eval:5» :: «tail:1») : (_root_.List _root_.Bool)))))))))))) | [] => .unmatch)


noncomputable def «Table_ok:one-default-action:iter:4_clauses» (input0 : (_root_.List tableProperty)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Table_ok:one-default-action:iter:4:clause:0»  input0), fun (_ : _root_.Unit) => («Table_ok:one-default-action:iter:4:clause:1»  input0)]

end SpecTec
