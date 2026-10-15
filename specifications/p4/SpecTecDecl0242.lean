import SpecTecDecl0241

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$instantiable_package:clause:0» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.instctxt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let instctxt : SpecTec.instctxt := input2; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))))


noncomputable def «$instantiable_package:clause:1» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.instctxt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let instctxt : SpecTec.instctxt := input2; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (let blockKind : SpecTec.blockKind := (blockTypingLayer.KIND (typingContext.BLOCK TC)); (.pure (((_root_.Decidable.decide (blockKind = ((SpecTec.blockKind.PACKAGE) : SpecTec.blockKind))) : _root_.Bool)))))))))


noncomputable def «$instantiable_package:clause:2» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.instctxt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let instctxt : SpecTec.instctxt := input2; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))))


noncomputable def «$instantiable_package_clauses» (input0 : cursor) (input1 : typingContext) (input2 : instctxt) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$instantiable_package:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$instantiable_package:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$instantiable_package:clause:2»  input0 input1 input2)]


noncomputable def «$instantiable_table:clause:0» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.instctxt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let instctxt : SpecTec.instctxt := input2; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))))


noncomputable def «$instantiable_table:clause:1» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.instctxt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let instctxt : SpecTec.instctxt := input2; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (let blockKind : SpecTec.blockKind := (blockTypingLayer.KIND (typingContext.BLOCK TC)); (.pure (((_root_.Decidable.decide (blockKind = ((SpecTec.blockKind.CONTROL) : SpecTec.blockKind))) : _root_.Bool)))))))))


noncomputable def «$instantiable_table:clause:2» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.instctxt) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let instctxt : SpecTec.instctxt := input2; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))))


noncomputable def «$instantiable_table_clauses» (input0 : cursor) (input1 : typingContext) (input2 : instctxt) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$instantiable_table:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$instantiable_table:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$instantiable_table:clause:2»  input0 input1 input2)]


noncomputable def «$callable_action:clause:0» (input0 : cursor) (input1 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))


noncomputable def «$callable_action:clause:1» (input0 : cursor) (input1 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))


noncomputable def «$callable_action:clause:2» (input0 : cursor) (input1 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (let localKind : SpecTec.localKind := (localTypingLayer.KIND (typingContext.LOCAL TC)); (.pure ((((_root_.Decidable.decide (localKind = ((SpecTec.localKind.ACTION) : SpecTec.localKind))) || (_root_.Decidable.decide (localKind = ((SpecTec.localKind.CONTROL_APPLY_METHOD) : SpecTec.localKind)))) : _root_.Bool))))))))


noncomputable def «$callable_action_clauses» (input0 : cursor) (input1 : typingContext) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$callable_action:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$callable_action:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$callable_action:clause:2»  input0 input1)]


noncomputable def «$callable_externFunction:clause:0» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let nameIR : SpecTec.nameIR := input2; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (.bind (.guard ("verify" = nameIR)) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))))))


noncomputable def «$callable_externFunction:clause:1» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let nameIR : SpecTec.nameIR := input2; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (.bind (.guard ((nameIR ≠ "verify"))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))))))


noncomputable def «$callable_externFunction:clause:2» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let nameIR : SpecTec.nameIR := input2; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (.bind (.guard ("verify" = nameIR)) (fun (_ : Unit) => (let blockKind : SpecTec.blockKind := (blockTypingLayer.KIND (typingContext.BLOCK TC)); (.pure (((_root_.Decidable.decide (blockKind = ((SpecTec.blockKind.PARSER) : SpecTec.blockKind))) : _root_.Bool)))))))))))


noncomputable def «$callable_externFunction:clause:3» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let nameIR : SpecTec.nameIR := input2; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (.bind (.guard ((nameIR ≠ "verify"))) (fun (_ : Unit) => (let blockKind : SpecTec.blockKind := (blockTypingLayer.KIND (typingContext.BLOCK TC)); (.pure ((((_root_.Decidable.decide (blockKind = ((SpecTec.blockKind.PARSER) : SpecTec.blockKind))) || (_root_.Decidable.decide (blockKind = ((SpecTec.blockKind.CONTROL) : SpecTec.blockKind)))) : _root_.Bool)))))))))))


noncomputable def «$callable_externFunction:clause:4» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let nameIR : SpecTec.nameIR := input2; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (.bind (.guard ("verify" = nameIR)) (fun (_ : Unit) => (let localKind : SpecTec.localKind := (localTypingLayer.KIND (typingContext.LOCAL TC)); (.pure (((_root_.Decidable.decide (localKind = ((SpecTec.localKind.PARSER_STATE) : SpecTec.localKind))) : _root_.Bool)))))))))))


noncomputable def «$callable_externFunction:clause:5» (input0 : cursor) (input1 : typingContext) (input2 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (let nameIR : SpecTec.nameIR := input2; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (.bind (.guard ((nameIR ≠ "verify"))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))))))


noncomputable def «$callable_externFunction_clauses» (input0 : cursor) (input1 : typingContext) (input2 : nameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$callable_externFunction:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («$callable_externFunction:clause:1»  input0 input1 input2), fun (_ : _root_.Unit) => («$callable_externFunction:clause:2»  input0 input1 input2), fun (_ : _root_.Unit) => («$callable_externFunction:clause:3»  input0 input1 input2), fun (_ : _root_.Unit) => («$callable_externFunction:clause:4»  input0 input1 input2), fun (_ : _root_.Unit) => («$callable_externFunction:clause:5»  input0 input1 input2)]


noncomputable def «$callable_externMethod:clause:0» (input0 : cursor) (input1 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))


noncomputable def «$callable_externMethod:clause:1» (input0 : cursor) (input1 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (let blockKind : SpecTec.blockKind := (blockTypingLayer.KIND (typingContext.BLOCK TC)); (.pure ((((_root_.Decidable.decide (blockKind = ((SpecTec.blockKind.PARSER) : SpecTec.blockKind))) || (_root_.Decidable.decide (blockKind = ((SpecTec.blockKind.CONTROL) : SpecTec.blockKind)))) : _root_.Bool))))))))


noncomputable def «$callable_externMethod:clause:2» (input0 : cursor) (input1 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))))


noncomputable def «$callable_externMethod_clauses» (input0 : cursor) (input1 : typingContext) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$callable_externMethod:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$callable_externMethod:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$callable_externMethod:clause:2»  input0 input1)]


noncomputable def «$callable_parserApplyMethod:clause:0» (input0 : cursor) (input1 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))


noncomputable def «$callable_parserApplyMethod:clause:1» (input0 : cursor) (input1 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))


noncomputable def «$callable_parserApplyMethod:clause:2» (input0 : cursor) (input1 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (let localKind : SpecTec.localKind := (localTypingLayer.KIND (typingContext.LOCAL TC)); (.pure (((_root_.Decidable.decide (localKind = ((SpecTec.localKind.PARSER_STATE) : SpecTec.localKind))) : _root_.Bool))))))))


noncomputable def «$callable_parserApplyMethod_clauses» (input0 : cursor) (input1 : typingContext) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$callable_parserApplyMethod:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$callable_parserApplyMethod:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$callable_parserApplyMethod:clause:2»  input0 input1)]


noncomputable def «$callable_controlApplyMethod:clause:0» (input0 : cursor) (input1 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))


noncomputable def «$callable_controlApplyMethod:clause:1» (input0 : cursor) (input1 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (.bind (.guard (((«exec:match:cursor:BLOCK» p) = true))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))


noncomputable def «$callable_controlApplyMethod:clause:2» (input0 : cursor) (input1 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (.bind (.guard (((«exec:match:cursor:LOCAL» p) = true))) (fun (_ : Unit) => (let localKind : SpecTec.localKind := (localTypingLayer.KIND (typingContext.LOCAL TC)); (.pure (((_root_.Decidable.decide (localKind = ((SpecTec.localKind.CONTROL_APPLY_METHOD) : SpecTec.localKind))) : _root_.Bool))))))))


noncomputable def «$callable_controlApplyMethod_clauses» (input0 : cursor) (input1 : typingContext) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$callable_controlApplyMethod:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$callable_controlApplyMethod:clause:1»  input0 input1), fun (_ : _root_.Unit) => («$callable_controlApplyMethod:clause:2»  input0 input1)]


noncomputable def «$callable_tableApplyMethod:clause:0» (input0 : cursor) (input1 : typingContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let p : cursor := input0; (let TC : typingContext := input1; (.bind (.guard (((«exec:match:cursor:GLOBAL» p) = true))) (fun (_ : Unit) => (.pure ((false : _root_.Bool)))))))

end SpecTec
