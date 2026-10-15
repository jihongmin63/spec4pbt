import SpecTecDecl0301

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$sizeof_minSizeInBits':case_13:iter:3:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨_root_.Nat, SpecTecCall.«$sizeof_minSizeInBits'» typeIR⟩) (fun («exec:3» : _root_.Nat) => (let «eval:4» : _root_.Nat := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$sizeof_minSizeInBits':case_13:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Nat)) => (let «tail:1» : (_root_.List _root_.Nat) := «exec:4»; (.pure (((«eval:4» :: «tail:1») : (_root_.List _root_.Nat)))))))))))) | [] => .unmatch)


noncomputable def «$sizeof_minSizeInBits':case_13:iter:3_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$sizeof_minSizeInBits':case_13:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$sizeof_minSizeInBits':case_13:iter:3:clause:1»  input0)]


noncomputable def «$sizeof_minSizeInBits:clause:0» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.call ⟨_root_.Nat, SpecTecCall.«$sizeof_minSizeInBits'» typeIR⟩) (fun («exec:1» : _root_.Nat) => (let «eval:0» : _root_.Nat := «exec:1»; (.pure ((((value.D (_root_.Int.ofNat «eval:0»)) : value) : value)))))))


noncomputable def «$sizeof_minSizeInBits_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$sizeof_minSizeInBits:clause:0»  input0)]


noncomputable def «$sizeof_minSizeInBytes:clause:0» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.call ⟨_root_.Nat, SpecTecCall.«$sizeof_minSizeInBits'» typeIR⟩) (fun («exec:1» : _root_.Nat) => (let «eval:0» : _root_.Nat := «exec:1»; (let n_size : _root_.Nat := «eval:0»; (.bind (SpecTecExecution.require (((8 : _root_.Nat) ≠ (0 : _root_.Nat))) "division by zero") (fun (_ : Unit) => (.pure ((((value.D (_root_.Int.ofNat (n_size / (8 : _root_.Nat)))) : value) : value))))))))))


noncomputable def «$sizeof_minSizeInBytes_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$sizeof_minSizeInBytes:clause:0»  input0)]


noncomputable def «$sizeof_maxSizeInBits':clause:0» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:boolTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$sizeof_maxSizeInBits':case_1:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : SpecTec.boolTypeIR := «exec:1»; (let boolTypeIR : SpecTec.boolTypeIR := «eval:0»; (.bind (.guard (((SpecTec.boolTypeIR.BOOL) : SpecTec.boolTypeIR) = boolTypeIR)) (fun (_ : Unit) => (.pure (((1 : _root_.Nat) : _root_.Nat))))))) | none => .unmatch))))


noncomputable def «$sizeof_maxSizeInBits':clause:1» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:fixedIntTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$sizeof_maxSizeInBits':case_2:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : fixedIntTypeIR := «exec:1»; (match «eval:0» with | .«INT `< % `>» «exec:2» => (let w : _root_.Nat := «exec:2»; (.pure ((w : _root_.Nat)))))) | none => .unmatch))))


noncomputable def «$sizeof_maxSizeInBits':clause:2» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:fixedBitTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$sizeof_maxSizeInBits':case_3:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : fixedBitTypeIR := «exec:1»; (match «eval:0» with | .«BIT `< % `>» «exec:2» => (let w : _root_.Nat := «exec:2»; (.pure ((w : _root_.Nat)))))) | none => .unmatch))))


noncomputable def «$sizeof_maxSizeInBits':clause:3» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:varBitTypeIR» typeIR) = true))) (fun (_ : Unit) => (match («$sizeof_maxSizeInBits':case_4:downcast:0» typeIR) with | some «exec:1» => (let «eval:0» : varBitTypeIR := «exec:1»; (match «eval:0» with | .«VARBIT `< % `>» «exec:2» => (let w : _root_.Nat := «exec:2»; (.pure ((w : _root_.Nat)))))) | none => .unmatch))))


noncomputable def «$sizeof_maxSizeInBits':clause:4» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:typedefTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$sizeof_maxSizeInBits':case_5:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : typedefTypeIR := «exec:1»; (match «eval:0» with | .TYPEDEF «exec:2» «exec:3» => (let _typeId : typeId := «exec:2»; (let typeIR : SpecTec.typeIR := «exec:3»; (.bind (.call ⟨_root_.Nat, SpecTecCall.«$sizeof_maxSizeInBits'» typeIR⟩) (fun («exec:4» : _root_.Nat) => (let «eval:1» : _root_.Nat := «exec:4»; (.pure ((«eval:1» : _root_.Nat)))))))))) | none => .unmatch))))


noncomputable def «$sizeof_maxSizeInBits':clause:5» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:newTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$sizeof_maxSizeInBits':case_6:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : newTypeIR := «exec:1»; (match «eval:0» with | .TYPE «exec:2» «exec:3» => (let _typeId : typeId := «exec:2»; (let typeIR : SpecTec.typeIR := «exec:3»; (.bind (.call ⟨_root_.Nat, SpecTecCall.«$sizeof_maxSizeInBits'» typeIR⟩) (fun («exec:4» : _root_.Nat) => (let «eval:1» : _root_.Nat := «exec:4»; (.pure ((«eval:1» : _root_.Nat)))))))))) | none => .unmatch))))


noncomputable def «$sizeof_maxSizeInBits':clause:6» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:serializableEnumTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$sizeof_maxSizeInBits':case_7:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : serializableEnumTypeIR := «exec:1»; (match «eval:0» with | .«ENUM % `< % `> `{ % `}» «exec:2» «exec:3» «exec:4» => (let _typeId : typeId := «exec:2»; (let typeIR : SpecTec.typeIR := «exec:3»; (let «_valueFieldIR*» : (_root_.List valueFieldIR) := «exec:4»; (.bind (.call ⟨_root_.Nat, SpecTecCall.«$sizeof_maxSizeInBits'» typeIR⟩) (fun («exec:5» : _root_.Nat) => (let «eval:1» : _root_.Nat := «exec:5»; (.pure ((«eval:1» : _root_.Nat))))))))))) | none => .unmatch))))


noncomputable def «$sizeof_maxSizeInBits':clause:7» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : typeIR := input0; (.bind (.guard (((«sub:typeIR:tupleTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$sizeof_maxSizeInBits':case_8:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : tupleTypeIR := «exec:1»; (match «eval:0» with | .«TUPLE `< % `>» «exec:2» => (let «typeIR*» : (_root_.List typeIR) := «exec:2»; (.bind (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$sizeof_maxSizeInBits':case_8:iter:1» «typeIR*»⟩) (fun («exec:3» : (_root_.List _root_.Nat)) => (let «eval:3» : (_root_.List _root_.Nat) := «exec:3»; (.pure (((«$sum_nat» «eval:3») : _root_.Nat))))))))) | none => .unmatch))))


noncomputable def «$sizeof_maxSizeInBits':clause:8» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:arrayTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$sizeof_maxSizeInBits':case_9:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : arrayTypeIR := «exec:1»; (match «eval:0» with | .«ARRAY % `[ % `]» «exec:2» «exec:3» => (let typeIR : SpecTec.typeIR := «exec:2»; (let n_size : _root_.Nat := «exec:3»; (.bind (.call ⟨_root_.Nat, SpecTecCall.«$sizeof_maxSizeInBits'» typeIR⟩) (fun («exec:4» : _root_.Nat) => (let «eval:1» : _root_.Nat := «exec:4»; (.pure (((«eval:1» * n_size) : _root_.Nat)))))))))) | none => .unmatch))))


noncomputable def «$sizeof_maxSizeInBits':clause:9» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : SpecTec.typeIR := input0; (.bind (.guard (((«sub:typeIR:headerStackTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$sizeof_maxSizeInBits':case_10:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : headerStackTypeIR := «exec:1»; (match «eval:0» with | .«HEADER_STACK % `[ % `]» «exec:2» «exec:3» => (let typeIR : SpecTec.typeIR := «exec:2»; (let n_size : _root_.Nat := «exec:3»; (.bind (.call ⟨_root_.Nat, SpecTecCall.«$sizeof_maxSizeInBits'» typeIR⟩) (fun («exec:4» : _root_.Nat) => (let «eval:1» : _root_.Nat := «exec:4»; (.pure (((«eval:1» * n_size) : _root_.Nat)))))))))) | none => .unmatch))))


noncomputable def «$sizeof_maxSizeInBits':clause:10» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : typeIR := input0; (.bind (.guard (((«sub:typeIR:structTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$sizeof_maxSizeInBits':case_11:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : structTypeIR := «exec:1»; (match «eval:0» with | .«STRUCT % `< % `> `{ % `}» «exec:2» «exec:3» «exec:4» => (let _typeId : typeId := «exec:2»; (let «_typeArgumentIR*» : (_root_.List typeArgumentIR) := «exec:3»; (let «eval:2» : (_root_.List fieldTypeIR) := «exec:4»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$sizeof_maxSizeInBits':case_11:pattern-iter:1» «eval:2»⟩) (fun («exec:5» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «_annotationList*» : (_root_.List annotationList) := («exec:5»).1; (let «_nameIR*» : (_root_.List nameIR) := ((«exec:5»).2).1; (let «typeIR*» : (_root_.List typeIR) := ((«exec:5»).2).2; (.bind (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$sizeof_maxSizeInBits':case_11:iter:3» «typeIR*»⟩) (fun («exec:6» : (_root_.List _root_.Nat)) => (let «eval:5» : (_root_.List _root_.Nat) := «exec:6»; (.pure (((«$sum_nat» «eval:5») : _root_.Nat)))))))))))))))) | none => .unmatch))))


noncomputable def «$sizeof_maxSizeInBits':clause:11» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : typeIR := input0; (.bind (.guard (((«sub:typeIR:headerTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$sizeof_maxSizeInBits':case_12:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : headerTypeIR := «exec:1»; (match «eval:0» with | .«HEADER % `< % `> `{ % `}» «exec:2» «exec:3» «exec:4» => (let _typeId : typeId := «exec:2»; (let «_typeArgumentIR*» : (_root_.List typeArgumentIR) := «exec:3»; (let «eval:2» : (_root_.List fieldTypeIR) := «exec:4»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$sizeof_maxSizeInBits':case_12:pattern-iter:1» «eval:2»⟩) (fun («exec:5» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «_annotationList*» : (_root_.List annotationList) := («exec:5»).1; (let «_nameIR*» : (_root_.List nameIR) := ((«exec:5»).2).1; (let «typeIR*» : (_root_.List typeIR) := ((«exec:5»).2).2; (.bind (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$sizeof_maxSizeInBits':case_12:iter:3» «typeIR*»⟩) (fun («exec:6» : (_root_.List _root_.Nat)) => (let «eval:5» : (_root_.List _root_.Nat) := «exec:6»; (.pure (((«$sum_nat» «eval:5») : _root_.Nat)))))))))))))))) | none => .unmatch))))


noncomputable def «$sizeof_maxSizeInBits':clause:12» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeIR' : typeIR := input0; (.bind (.guard (((«sub:typeIR:headerUnionTypeIR» typeIR') = true))) (fun (_ : Unit) => (match («$sizeof_maxSizeInBits':case_13:downcast:0» typeIR') with | some «exec:1» => (let «eval:0» : headerUnionTypeIR := «exec:1»; (match «eval:0» with | .«HEADER_UNION % `< % `> `{ % `}» «exec:2» «exec:3» «exec:4» => (let _typeId : typeId := «exec:2»; (let «_typeArgumentIR*» : (_root_.List typeArgumentIR) := «exec:3»; (let «eval:2» : (_root_.List fieldTypeIR) := «exec:4»; (.bind (.call ⟨((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR))), SpecTecCall.«$sizeof_maxSizeInBits':case_13:pattern-iter:1» «eval:2»⟩) (fun («exec:5» : ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))) => (let «_annotationList*» : (_root_.List annotationList) := («exec:5»).1; (let «_nameIR*» : (_root_.List nameIR) := ((«exec:5»).2).1; (let «typeIR*» : (_root_.List typeIR) := ((«exec:5»).2).2; (.bind (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$sizeof_maxSizeInBits':case_13:iter:3» «typeIR*»⟩) (fun («exec:6» : (_root_.List _root_.Nat)) => (let «eval:5» : (_root_.List _root_.Nat) := «exec:6»; (.bind (.call ⟨_root_.Nat, SpecTecCall.«$max_nat» «eval:5»⟩) (fun («exec:7» : _root_.Nat) => (let «eval:6» : _root_.Nat := «exec:7»; (.pure ((«eval:6» : _root_.Nat))))))))))))))))))) | none => .unmatch))))


noncomputable def «$sizeof_maxSizeInBits'_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':clause:0»  input0), fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':clause:1»  input0), fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':clause:2»  input0), fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':clause:3»  input0), fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':clause:4»  input0), fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':clause:5»  input0), fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':clause:6»  input0), fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':clause:7»  input0), fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':clause:8»  input0), fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':clause:9»  input0), fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':clause:10»  input0), fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':clause:11»  input0), fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':clause:12»  input0)]


noncomputable def «$sizeof_maxSizeInBits':case_8:iter:1:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Nat)) : (_root_.List _root_.Nat)))) | _ :: _ => .unmatch)


noncomputable def «$sizeof_maxSizeInBits':case_8:iter:1:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨_root_.Nat, SpecTecCall.«$sizeof_maxSizeInBits'» typeIR⟩) (fun («exec:3» : _root_.Nat) => (let «eval:2» : _root_.Nat := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$sizeof_maxSizeInBits':case_8:iter:1» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Nat)) => (let «tail:1» : (_root_.List _root_.Nat) := «exec:4»; (.pure (((«eval:2» :: «tail:1») : (_root_.List _root_.Nat)))))))))))) | [] => .unmatch)


noncomputable def «$sizeof_maxSizeInBits':case_8:iter:1_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':case_8:iter:1:clause:0»  input0), fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':case_8:iter:1:clause:1»  input0)]


noncomputable def «$sizeof_maxSizeInBits':case_11:iter:3:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Nat)) : (_root_.List _root_.Nat)))) | _ :: _ => .unmatch)


noncomputable def «$sizeof_maxSizeInBits':case_11:iter:3:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨_root_.Nat, SpecTecCall.«$sizeof_maxSizeInBits'» typeIR⟩) (fun («exec:3» : _root_.Nat) => (let «eval:4» : _root_.Nat := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$sizeof_maxSizeInBits':case_11:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Nat)) => (let «tail:1» : (_root_.List _root_.Nat) := «exec:4»; (.pure (((«eval:4» :: «tail:1») : (_root_.List _root_.Nat)))))))))))) | [] => .unmatch)


noncomputable def «$sizeof_maxSizeInBits':case_11:iter:3_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':case_11:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':case_11:iter:3:clause:1»  input0)]


noncomputable def «$sizeof_maxSizeInBits':case_12:iter:3:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Nat)) : (_root_.List _root_.Nat)))) | _ :: _ => .unmatch)


noncomputable def «$sizeof_maxSizeInBits':case_12:iter:3:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨_root_.Nat, SpecTecCall.«$sizeof_maxSizeInBits'» typeIR⟩) (fun («exec:3» : _root_.Nat) => (let «eval:4» : _root_.Nat := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$sizeof_maxSizeInBits':case_12:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Nat)) => (let «tail:1» : (_root_.List _root_.Nat) := «exec:4»; (.pure (((«eval:4» :: «tail:1») : (_root_.List _root_.Nat)))))))))))) | [] => .unmatch)


noncomputable def «$sizeof_maxSizeInBits':case_12:iter:3_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':case_12:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':case_12:iter:3:clause:1»  input0)]


noncomputable def «$sizeof_maxSizeInBits':case_13:iter:3:clause:0» (input0 : (_root_.List typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List _root_.Nat)) : (_root_.List _root_.Nat)))) | _ :: _ => .unmatch)


noncomputable def «$sizeof_maxSizeInBits':case_13:iter:3:clause:1» (input0 : (_root_.List SpecTec.typeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let typeIR : SpecTec.typeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.typeIR) := «exec:1»; (.bind (.call ⟨_root_.Nat, SpecTecCall.«$sizeof_maxSizeInBits'» typeIR⟩) (fun («exec:3» : _root_.Nat) => (let «eval:4» : _root_.Nat := «exec:3»; (.bind (.call ⟨(_root_.List _root_.Nat), SpecTecCall.«$sizeof_maxSizeInBits':case_13:iter:3» «tail:0»⟩) (fun («exec:4» : (_root_.List _root_.Nat)) => (let «tail:1» : (_root_.List _root_.Nat) := «exec:4»; (.pure (((«eval:4» :: «tail:1») : (_root_.List _root_.Nat)))))))))))) | [] => .unmatch)


noncomputable def «$sizeof_maxSizeInBits':case_13:iter:3_clauses» (input0 : (_root_.List typeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':case_13:iter:3:clause:0»  input0), fun (_ : _root_.Unit) => («$sizeof_maxSizeInBits':case_13:iter:3:clause:1»  input0)]

end SpecTec
