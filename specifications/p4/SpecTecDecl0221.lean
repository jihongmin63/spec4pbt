import SpecTecDecl0220

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

noncomputable def «$merge_frames:clause:0» (input0 : SpecTec.frame) (input1 : SpecTec.frame) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let frame : SpecTec.frame := input0; (match input1 with | .«`{ % `}» «exec:1» => (let «eval:1» : (_root_.List (pair id value)) := «exec:1»; (.bind (.call ⟨((_root_.List id) × (_root_.List value)), SpecTecCall.«$merge_frames:case_1:pattern-iter:0» «eval:1»⟩) (fun («exec:2» : ((_root_.List id) × (_root_.List value))) => (let «id*» : (_root_.List id) := («exec:2»).1; (let «value*» : (_root_.List value) := («exec:2»).2; (.bind (.call ⟨(map id value), SpecTecCall.«$adds_map» id value frame «id*» «value*»⟩) (fun («exec:3» : (map id value)) => (let «eval:2» : (map id value) := «exec:3»; (.pure ((«eval:2» : SpecTec.frame)))))))))))))


noncomputable def «$merge_frames_clauses» (input0 : frame) (input1 : frame) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$merge_frames:clause:0»  input0 input1)]


noncomputable def «$merge_externMethodDefEnvs:case_2:pattern-iter:0:clause:0» (input0 : (_root_.List (pair callTargetId callableDef))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure (((([] : (_root_.List callableDef)), ([] : (_root_.List callableId))) : ((_root_.List callableDef) × (_root_.List callableId))))) | _ :: _ => .unmatch)


noncomputable def «$merge_externMethodDefEnvs:case_2:pattern-iter:0:clause:1» (input0 : (_root_.List (pair callTargetId callableDef))) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (match «exec:2» with | .«% ':' %» «exec:3» «exec:4» => (let callableId_t : callableId := «exec:3»; (let callableDef_t : callableDef := «exec:4»; (let «pattern-tail:0» : (_root_.List (pair callTargetId callableDef)) := «exec:1»; (.bind (.call ⟨((_root_.List callableDef) × (_root_.List callableId)), SpecTecCall.«$merge_externMethodDefEnvs:case_2:pattern-iter:0» «pattern-tail:0»⟩) (fun («exec:5» : ((_root_.List callableDef) × (_root_.List callableId))) => (let «pattern-tail:1» : (_root_.List callableDef) := («exec:5»).1; (let «pattern-tail:2» : (_root_.List callableId) := («exec:5»).2; (.pure ((((callableDef_t :: «pattern-tail:1»), (callableId_t :: «pattern-tail:2»)) : ((_root_.List callableDef) × (_root_.List callableId))))))))))))) | [] => .unmatch)


noncomputable def «$merge_externMethodDefEnvs:case_2:pattern-iter:0_clauses» (input0 : (_root_.List (pair callTargetId callableDef))) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$merge_externMethodDefEnvs:case_2:pattern-iter:0:clause:0»  input0), fun (_ : _root_.Unit) => («$merge_externMethodDefEnvs:case_2:pattern-iter:0:clause:1»  input0)]


noncomputable def «$merge_externMethodDefEnvs:case_2:iter:4:clause:0» (input0 : (_root_.List callableDef)) (input1 : (_root_.List callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (match input1 with | [] => (.pure ((([] : (_root_.List (pair callTargetId callableDef))) : (_root_.List (pair callTargetId callableDef))))) | _ :: _ => .unmatch) | _ :: _ => .unmatch)


noncomputable def «$merge_externMethodDefEnvs:case_2:iter:4:clause:1» (input0 : (_root_.List callableDef)) (input1 : (_root_.List callableId)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let callableDef_t : callableDef := «exec:2»; (let «tail:0» : (_root_.List callableDef) := «exec:1»; (match input1 with | «exec:4» :: «exec:3» => (let callableId_t : callableId := «exec:4»; (let «tail:1» : (_root_.List callableId) := «exec:3»; (.bind (.call ⟨(_root_.List (pair callTargetId callableDef)), SpecTecCall.«$merge_externMethodDefEnvs:case_2:iter:4» «tail:0» «tail:1»⟩) (fun («exec:5» : (_root_.List (pair callTargetId callableDef))) => (let «tail:2» : (_root_.List (pair callTargetId callableDef)) := «exec:5»; (.pure (((((pair.«% ':' %» callableId_t callableDef_t) : (pair callableId callableDef)) :: «tail:2») : (_root_.List (pair callTargetId callableDef)))))))))) | [] => .unmatch))) | [] => .unmatch)


noncomputable def «$merge_externMethodDefEnvs:case_2:iter:4_clauses» (input0 : (_root_.List callableDef)) (input1 : (_root_.List callableId)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$merge_externMethodDefEnvs:case_2:iter:4:clause:0»  input0 input1), fun (_ : _root_.Unit) => («$merge_externMethodDefEnvs:case_2:iter:4:clause:1»  input0 input1)]


noncomputable def «$callableId_of_externConstructorPrototypeIR:clause:0» (input0 : externConstructorPrototypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | .«% % `< ',' % `> `( % `) ';'» «exec:1» «exec:2» «exec:3» «exec:4» => (let _annotationList : annotationList := «exec:1»; (let nameIR : SpecTec.nameIR := «exec:2»; (let _typeParameterListIR : typeParameterListIR := «exec:3»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:4»; (.bind (.call ⟨callableId, SpecTecCall.«$callableId_IR» nameIR «parameterIR*»⟩) (fun («exec:5» : callableId) => (let «eval:0» : callableId := «exec:5»; (.pure ((«eval:0» : callableId)))))))))))


noncomputable def «$callableId_of_externConstructorPrototypeIR_clauses» (input0 : externConstructorPrototypeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$callableId_of_externConstructorPrototypeIR:clause:0»  input0)]


noncomputable def «Decl_inst:constructor:iter:8:clause:0» (input0 : (_root_.List externConstructorPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | [] => (.pure ((([] : (_root_.List callableId)) : (_root_.List callableId)))) | _ :: _ => .unmatch)


noncomputable def «Decl_inst:constructor:iter:8:clause:1» (input0 : (_root_.List SpecTec.externConstructorPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let externConstructorPrototypeIR : SpecTec.externConstructorPrototypeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.externConstructorPrototypeIR) := «exec:1»; (.bind (.call ⟨callableId, SpecTecCall.«$callableId_of_externConstructorPrototypeIR» externConstructorPrototypeIR⟩) (fun («exec:3» : callableId) => (let «eval:9» : callableId := «exec:3»; (let callableId_constructor : callableId := «eval:9»; (.bind (.call ⟨(_root_.List callableId), SpecTecCall.«Decl_inst:constructor:iter:8» «tail:0»⟩) (fun («exec:4» : (_root_.List callableId)) => (let «tail:1» : (_root_.List callableId) := «exec:4»; (.pure (((callableId_constructor :: «tail:1») : (_root_.List callableId))))))))))))) | [] => .unmatch)


noncomputable def «Decl_inst:constructor:iter:8_clauses» (input0 : (_root_.List externConstructorPrototypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:constructor:iter:8:clause:0»  input0), fun (_ : _root_.Unit) => («Decl_inst:constructor:iter:8:clause:1»  input0)]


noncomputable def «$constructor_of_externConstructorPrototypeIR:clause:0» (input0 : SpecTec.typeParameterListIR) (input1 : SpecTec.externMethodPrototypeListIR) (input2 : externConstructorPrototypeIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeParameterListIR_expl : SpecTec.typeParameterListIR := input0; (let externMethodPrototypeListIR : SpecTec.externMethodPrototypeListIR := input1; (match input2 with | .«% % `< ',' % `> `( % `) ';'» «exec:1» «exec:2» «exec:3» «exec:4» => (let _annotationList : annotationList := «exec:1»; (let nameIR : SpecTec.nameIR := «exec:2»; (let typeParameterListIR_impl : SpecTec.typeParameterListIR := «exec:3»; (let «parameterIR*» : (_root_.List parameterIR) := «exec:4»; (let typeParameterListIR : SpecTec.typeParameterListIR := (typeParameterListIR_expl ++ typeParameterListIR_impl); (let constructorDef : SpecTec.constructorDef := ((SpecTec.constructorDef.«EXTERN % `< % `> `( % `) `{ % `}» nameIR typeParameterListIR «parameterIR*» externMethodPrototypeListIR) : SpecTec.constructorDef); (.pure ((constructorDef : SpecTec.constructorDef))))))))))))


noncomputable def «$constructor_of_externConstructorPrototypeIR_clauses» (input0 : typeParameterListIR) (input1 : externMethodPrototypeListIR) (input2 : externConstructorPrototypeIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$constructor_of_externConstructorPrototypeIR:clause:0»  input0 input1 input2)]


noncomputable def «Decl_inst:constructor:iter:10:clause:0» (input0 : SpecTec.typeParameterListIR) (input1 : (_root_.List externMethodPrototypeIR)) (input2 : (_root_.List externConstructorPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeParameterListIR : SpecTec.typeParameterListIR := input0; (let «externMethodPrototypeIR*» : (_root_.List externMethodPrototypeIR) := input1; (match input2 with | [] => (.pure ((([] : (_root_.List constructorDef)) : (_root_.List constructorDef)))) | _ :: _ => .unmatch)))


noncomputable def «Decl_inst:constructor:iter:10:clause:1» (input0 : SpecTec.typeParameterListIR) (input1 : (_root_.List externMethodPrototypeIR)) (input2 : (_root_.List SpecTec.externConstructorPrototypeIR)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let typeParameterListIR : SpecTec.typeParameterListIR := input0; (let «externMethodPrototypeIR*» : (_root_.List externMethodPrototypeIR) := input1; (match input2 with | «exec:2» :: «exec:1» => (let externConstructorPrototypeIR : SpecTec.externConstructorPrototypeIR := «exec:2»; (let «tail:0» : (_root_.List SpecTec.externConstructorPrototypeIR) := «exec:1»; (.bind (.call ⟨SpecTec.constructorDef, SpecTecCall.«$constructor_of_externConstructorPrototypeIR» typeParameterListIR «externMethodPrototypeIR*» externConstructorPrototypeIR⟩) (fun («exec:3» : SpecTec.constructorDef) => (let «eval:11» : SpecTec.constructorDef := «exec:3»; (let constructorDef : SpecTec.constructorDef := «eval:11»; (.bind (.call ⟨(_root_.List SpecTec.constructorDef), SpecTecCall.«Decl_inst:constructor:iter:10» typeParameterListIR «externMethodPrototypeIR*» «tail:0»⟩) (fun («exec:4» : (_root_.List SpecTec.constructorDef)) => (let «tail:1» : (_root_.List SpecTec.constructorDef) := «exec:4»; (.pure (((constructorDef :: «tail:1») : (_root_.List SpecTec.constructorDef))))))))))))) | [] => .unmatch)))


noncomputable def «Decl_inst:constructor:iter:10_clauses» (input0 : typeParameterListIR) (input1 : (_root_.List externMethodPrototypeIR)) (input2 : (_root_.List externConstructorPrototypeIR)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («Decl_inst:constructor:iter:10:clause:0»  input0 input1 input2), fun (_ : _root_.Unit) => («Decl_inst:constructor:iter:10:clause:1»  input0 input1 input2)]


noncomputable def «$enter_e:clause:0» (input0 : evalContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let EC : evalContext := input0; (.bind (.call ⟨frame, SpecTecCall.«$empty_frame»⟩) (fun («exec:1» : frame) => (let «eval:0» : frame := «exec:1»; (.pure ((({ EC with LOCAL := ({ (evalContext.LOCAL EC) with FRAMES := («eval:0» :: (localInstLayer.FRAMES (evalContext.LOCAL EC))) } : localInstLayer) } : evalContext) : evalContext)))))))


noncomputable def «$enter_e_clauses» (input0 : evalContext) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$enter_e:clause:0»  input0)]


noncomputable def «$exit_e:clause:0» (input0 : evalContext) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let EC : evalContext := input0; (let «frame*» : (_root_.List frame) := (localInstLayer.FRAMES (evalContext.LOCAL EC)); (.bind (.guard (((_root_.Decidable.decide ((_root_.List.length «frame*») > (0 : _root_.Nat))) = true))) (fun (_ : Unit) => (match «frame*» with | «exec:2» :: «exec:1» => (let frame_h : frame := «exec:2»; (let «frame_t*» : (_root_.List frame) := «exec:1»; (.pure ((({ EC with LOCAL := ({ (evalContext.LOCAL EC) with FRAMES := «frame_t*» } : localInstLayer) } : evalContext) : evalContext))))) | [] => .unmatch)))))


noncomputable def «$exit_e_clauses» (input0 : evalContext) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$exit_e:clause:0»  input0)]


noncomputable def «$find_parserState_e:clause:0» (input0 : evalContext) (input1 : SpecTec.nameIR) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let EC : evalContext := input0; (let nameIR : SpecTec.nameIR := input1; (.bind (.call ⟨(_root_.Option parserStateIR), SpecTecCall.«$find_map» SpecTec.nameIR parserStateIR (blockInstLayer.STATE (evalContext.BLOCK EC)) nameIR⟩) (fun («exec:1» : (_root_.Option parserStateIR)) => (let «eval:0» : (_root_.Option parserStateIR) := «exec:1»; (.pure ((«eval:0» : (_root_.Option parserStateIR)))))))))


noncomputable def «$find_parserState_e_clauses» (input0 : evalContext) (input1 : nameIR) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_parserState_e:clause:0»  input0 input1)]


noncomputable def «$add_object_e:clause:0» (input0 : arch) (input1 : SpecTec.objectId) (input2 : SpecTec.object) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let ARCH : arch := input0; (let objectId : SpecTec.objectId := input1; (let object : SpecTec.object := input2; (.bind (.call ⟨(map SpecTec.objectId SpecTec.object), SpecTecCall.«$add_map» SpecTec.objectId SpecTec.object (arch.STORE ARCH) objectId object⟩) (fun («exec:1» : (map SpecTec.objectId SpecTec.object)) => (let «eval:0» : (map SpecTec.objectId SpecTec.object) := «exec:1»; (let STO : store := «eval:0»; (.pure ((({ ARCH with STORE := STO } : arch) : arch))))))))))


noncomputable def «$add_object_e_clauses» (input0 : arch) (input1 : objectId) (input2 : object) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$add_object_e:clause:0»  input0 input1 input2)]


noncomputable def «$find_archState_e:clause:0» (input0 : arch) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let ARCH : arch := input0; (.pure (((arch.STATE ARCH) : archState))))


noncomputable def «$find_archState_e_clauses» (input0 : arch) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_archState_e:clause:0»  input0)]


noncomputable def «$find_object_e:clause:0» (input0 : arch) (input1 : SpecTec.objectId) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let ARCH : arch := input0; (let objectId : SpecTec.objectId := input1; (.bind (.call ⟨(_root_.Option object), SpecTecCall.«$find_map» SpecTec.objectId object (arch.STORE ARCH) objectId⟩) (fun («exec:1» : (_root_.Option object)) => (let «eval:0» : (_root_.Option object) := «exec:1»; (.pure ((«eval:0» : (_root_.Option object)))))))))


noncomputable def «$find_object_e_clauses» (input0 : arch) (input1 : objectId) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_object_e:clause:0»  input0 input1)]


noncomputable def «$find_object_qualified_e:clause:0» (input0 : arch) (input1 : SpecTec.objectId) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let ARCH : arch := input0; (let objectId : SpecTec.objectId := input1; (.bind (.call ⟨(_root_.Option object), SpecTecCall.«$find_object_e» ARCH objectId⟩) (fun («exec:1» : (_root_.Option object)) => (let «eval:0» : (_root_.Option object) := «exec:1»; (.pure ((«eval:0» : (_root_.Option object)))))))))


noncomputable def «$find_object_qualified_e_clauses» (input0 : arch) (input1 : objectId) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$find_object_qualified_e:clause:0»  input0 input1)]

end SpecTec
