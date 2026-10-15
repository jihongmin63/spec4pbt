import SpecTecDecl0172

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$nestable_new:clause:5» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let newTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_new:matches:5:row» newTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_new:clause:6» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_new:matches:6:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$nestable_new_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$nestable_new:clause:0»  input0), fun (_ : _root_.Unit) => («$nestable_new:clause:1»  input0), fun (_ : _root_.Unit) => («$nestable_new:clause:2»  input0), fun (_ : _root_.Unit) => («$nestable_new:clause:3»  input0), fun (_ : _root_.Unit) => («$nestable_new:clause:4»  input0), fun (_ : _root_.Unit) => («$nestable_new:clause:5»  input0), fun (_ : _root_.Unit) => («$nestable_new:clause:6»  input0)]


noncomputable def «$nestable_list:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .BOOL  => (.bind (.guard ((0 : _root_.Nat) = («$nestable_list:matches:0:row» ((typeIR.BOOL) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$nestable_list:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .ERROR  => (.bind (.guard ((0 : _root_.Nat) = («$nestable_list:matches:1:row» ((typeIR.ERROR) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$nestable_list:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .MATCH_KIND  => (.bind (.guard ((0 : _root_.Nat) = («$nestable_list:matches:2:row» ((typeIR.MATCH_KIND) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$nestable_list:clause:3» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .STRING  => (.bind (.guard ((0 : _root_.Nat) = («$nestable_list:matches:3:row» ((typeIR.STRING) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$nestable_list:clause:4» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let integerTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_list:matches:4:row» integerTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_list:clause:5» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_list:matches:5:row» nameTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_list:clause:6» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_list:matches:6:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_list» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$nestable_list:clause:7» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let newTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_list:matches:7:row» newTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_list:clause:8» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let listTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_list:matches:8:row» listTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_list:clause:9» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let tupleTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_list:matches:9:row» tupleTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_list:clause:10» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let headerStackTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_list:matches:10:row» headerStackTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_list:clause:11» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let structTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_list:matches:11:row» structTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_list:clause:12» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let headerTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_list:matches:12:row» headerTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_list:clause:13» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let headerUnionTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_list:matches:13:row» headerUnionTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_list:clause:14» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let enumTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_list:matches:14:row» enumTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_list:clause:15» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_list:matches:15:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$nestable_list_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$nestable_list:clause:0»  input0), fun (_ : _root_.Unit) => («$nestable_list:clause:1»  input0), fun (_ : _root_.Unit) => («$nestable_list:clause:2»  input0), fun (_ : _root_.Unit) => («$nestable_list:clause:3»  input0), fun (_ : _root_.Unit) => («$nestable_list:clause:4»  input0), fun (_ : _root_.Unit) => («$nestable_list:clause:5»  input0), fun (_ : _root_.Unit) => («$nestable_list:clause:6»  input0), fun (_ : _root_.Unit) => («$nestable_list:clause:7»  input0), fun (_ : _root_.Unit) => («$nestable_list:clause:8»  input0), fun (_ : _root_.Unit) => («$nestable_list:clause:9»  input0), fun (_ : _root_.Unit) => («$nestable_list:clause:10»  input0), fun (_ : _root_.Unit) => («$nestable_list:clause:11»  input0), fun (_ : _root_.Unit) => («$nestable_list:clause:12»  input0), fun (_ : _root_.Unit) => («$nestable_list:clause:13»  input0), fun (_ : _root_.Unit) => («$nestable_list:clause:14»  input0), fun (_ : _root_.Unit) => («$nestable_list:clause:15»  input0)]


noncomputable def «$nestable_array_in_tuple:clause:0» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .BOOL  => (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_tuple:matches:0:row» ((typeIR.BOOL) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))) | _ => .unmatch)


noncomputable def «$nestable_array_in_tuple:clause:1» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«INT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_tuple:matches:1:row» ((typeIR.«INT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$nestable_array_in_tuple:clause:2» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«BIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_tuple:matches:2:row» ((typeIR.«BIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$nestable_array_in_tuple:clause:3» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«VARBIT `< % `>» «exec:1» => (let _nat : _root_.Nat := «exec:1»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_tuple:matches:3:row» ((typeIR.«VARBIT `< % `>» _nat) : typeIR)))) (fun (_ : Unit) => (.pure ((true : _root_.Bool)))))) | _ => .unmatch)


noncomputable def «$nestable_array_in_tuple:clause:4» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let nameTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_tuple:matches:4:row» nameTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_array_in_tuple:clause:5» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .TYPEDEF «exec:1» «exec:2» => (let _typeId : typeId := «exec:1»; (let typeIR : SpecTec.typeIR := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_tuple:matches:5:row» ((SpecTec.typeIR.TYPEDEF _typeId typeIR) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_array_in_tuple» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$nestable_array_in_tuple:clause:6» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let newTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_tuple:matches:6:row» newTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_array_in_tuple:clause:7» (input0 : SpecTec.typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«ARRAY % `[ % `]» «exec:1» «exec:2» => (let typeIR : SpecTec.typeIR := «exec:1»; (let _nat : _root_.Nat := «exec:2»; (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_tuple:matches:7:row» ((SpecTec.typeIR.«ARRAY % `[ % `]» typeIR _nat) : SpecTec.typeIR)))) (fun (_ : Unit) => (.bind (.call ⟨_root_.Bool, SpecTecCall.«$nestable_array_in_tuple» typeIR⟩) (fun («exec:3» : _root_.Bool) => (let «eval:0» : _root_.Bool := «exec:3»; (.pure ((«eval:0» : _root_.Bool)))))))))) | _ => .unmatch)


noncomputable def «$nestable_array_in_tuple:clause:8» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let structTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_tuple:matches:8:row» structTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_array_in_tuple:clause:9» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let enumTypeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_tuple:matches:9:row» enumTypeIR))) (fun (_ : Unit) => (.pure ((true : _root_.Bool))))))


noncomputable def «$nestable_array_in_tuple:clause:10» (input0 : typeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let _typeIR : typeIR := input0; (.bind (.guard ((0 : _root_.Nat) = («$nestable_array_in_tuple:matches:10:row» _typeIR))) (fun (_ : Unit) => (.pure ((false : _root_.Bool))))))


noncomputable def «$nestable_array_in_tuple_clauses» (input0 : typeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$nestable_array_in_tuple:clause:0»  input0), fun (_ : _root_.Unit) => («$nestable_array_in_tuple:clause:1»  input0), fun (_ : _root_.Unit) => («$nestable_array_in_tuple:clause:2»  input0), fun (_ : _root_.Unit) => («$nestable_array_in_tuple:clause:3»  input0), fun (_ : _root_.Unit) => («$nestable_array_in_tuple:clause:4»  input0), fun (_ : _root_.Unit) => («$nestable_array_in_tuple:clause:5»  input0), fun (_ : _root_.Unit) => («$nestable_array_in_tuple:clause:6»  input0), fun (_ : _root_.Unit) => («$nestable_array_in_tuple:clause:7»  input0), fun (_ : _root_.Unit) => («$nestable_array_in_tuple:clause:8»  input0), fun (_ : _root_.Unit) => («$nestable_array_in_tuple:clause:9»  input0), fun (_ : _root_.Unit) => («$nestable_array_in_tuple:clause:10»  input0)]

end SpecTec
