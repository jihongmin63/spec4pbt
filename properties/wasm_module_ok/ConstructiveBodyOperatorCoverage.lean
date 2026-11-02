import properties.wasm_module_ok.ConstructiveBodyPayloadCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyOperatorCoverage
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyProductionCoverage ConstructiveBodyOperatorProductions ConstructiveBodyOperatorEnums ConstructiveBodyOperatorDomains ConstructiveBodyOperatorTypes ConstructiveConstTableCore

theorem vecTest (c : context) (stack : inferresulttype) (env : Env c) (op : vtestop_) :
    ∃p∈all c stack env,Produces p (.«VEC.TEST» op) := by
  refine ⟨ConstructiveBodyOperatorProductions.vecTest c stack env,?_,?_⟩
  · apply List.mem_append_left
    apply List.mem_append_right
    simp
  · unfold ConstructiveBodyOperatorProductions.vecTest
    apply ConstructiveBodyPayloadCoverage.mapped
    exact generate_support vec_tests op

theorem vecUnary (c : context) (stack : inferresulttype) (env : Env c) (op : vunop_) :
    ∃p∈all c stack env,Produces p (.«VEC.UNARY» op) := by
  refine ⟨ConstructiveBodyOperatorProductions.vecUnary c stack env,?_,?_⟩
  · apply List.mem_append_left
    apply List.mem_append_right
    simp
  · unfold ConstructiveBodyOperatorProductions.vecUnary
    apply ConstructiveBodyPayloadCoverage.mapped
    exact generate_support vec_unaries op

theorem vecTernary (c : context) (stack : inferresulttype) (env : Env c) (op : vternop_) :
    ∃p∈all c stack env,Produces p (.«VEC.TERNARY» op) := by
  refine ⟨ConstructiveBodyOperatorProductions.vecTernary c stack env,?_,?_⟩
  · apply List.mem_append_left
    apply List.mem_append_right
    simp
  · unfold ConstructiveBodyOperatorProductions.vecTernary
    apply ConstructiveBodyPayloadCoverage.mapped
    exact generate_support vec_ternaries op

theorem vecCompare (c : context) (stack : inferresulttype) (env : Env c) (op : vrelop_) :
    ∃p∈all c stack env,Produces p (.«VEC.COMPARE» op) := by
  refine ⟨ConstructiveBodyOperatorProductions.vecCompare c stack env,?_,?_⟩
  · apply List.mem_append_left
    apply List.mem_append_right
    simp
  · unfold ConstructiveBodyOperatorProductions.vecCompare
    apply ConstructiveBodyPayloadCoverage.mapped
    exact generate_support vec_comparisons op

theorem vecConvert (c : context) (stack : inferresulttype) (env : Env c) (op : vcvtop_) :
    ∃p∈all c stack env,Produces p (.«VEC.CONVERT» op) := by
  refine ⟨ConstructiveBodyOperatorProductions.vecConvert c stack env,?_,?_⟩
  · apply List.mem_append_left
    apply List.mem_append_right
    simp
  · unfold ConstructiveBodyOperatorProductions.vecConvert
    apply ConstructiveBodyPayloadCoverage.mapped
    exact generate_support vec_conversions op

theorem vecShift (c : context) (stack : inferresulttype) (env : Env c) (op : vshiftop_) :
    ∃p∈all c stack env,Produces p (.«VEC.SHIFT» op) := by
  refine ⟨ConstructiveBodyOperatorProductions.vecShift c stack env,?_,?_⟩
  · apply List.mem_append_left
    apply List.mem_append_right
    simp
  · unfold ConstructiveBodyOperatorProductions.vecShift
    apply ConstructiveBodyPayloadCoverage.mapped
    exact generate_support vec_shifts op

theorem vecBitmask (c : context) (stack : inferresulttype) (env : Env c) (op : vbitmaskop_) :
    ∃p∈all c stack env,Produces p (.«VEC.BITMASK» op) := by
  refine ⟨ConstructiveBodyOperatorProductions.vecBitmask c stack env,?_,?_⟩
  · apply List.mem_append_left
    apply List.mem_append_right
    simp
  · unfold ConstructiveBodyOperatorProductions.vecBitmask
    apply ConstructiveBodyPayloadCoverage.mapped
    exact generate_support vec_bitmasks op

theorem vecTestbits (c : context) (stack : inferresulttype) (env : Env c) (op : vvtestop_) :
    ∃p∈all c stack env,Produces p (.«VEC.TESTBITS» op) := by
  refine ⟨ConstructiveBodyOperatorProductions.vecTestbits c stack env,?_,?_⟩
  · apply List.mem_append_left
    apply List.mem_append_right
    simp
  · unfold ConstructiveBodyOperatorProductions.vecTestbits
    apply ConstructiveBodyPayloadCoverage.mapped
    exact generate_support vvtestops op

theorem vecUnarybits (c : context) (stack : inferresulttype) (env : Env c) (op : vvunop_) :
    ∃p∈all c stack env,Produces p (.«VEC.UNARYBITS» op) := by
  refine ⟨ConstructiveBodyOperatorProductions.vecUnarybits c stack env,?_,?_⟩
  · apply List.mem_append_left
    apply List.mem_append_right
    simp
  · unfold ConstructiveBodyOperatorProductions.vecUnarybits
    apply ConstructiveBodyPayloadCoverage.mapped
    exact generate_support vvunops op

theorem vecBinarybits (c : context) (stack : inferresulttype) (env : Env c) (op : vvbinop_) :
    ∃p∈all c stack env,Produces p (.«VEC.BINARYBITS» op) := by
  refine ⟨ConstructiveBodyOperatorProductions.vecBinarybits c stack env,?_,?_⟩
  · apply List.mem_append_left
    apply List.mem_append_right
    simp
  · unfold ConstructiveBodyOperatorProductions.vecBinarybits
    apply ConstructiveBodyPayloadCoverage.mapped
    exact generate_support vvbinops op

theorem vecTernarybits (c : context) (stack : inferresulttype) (env : Env c) (op : vvternop_) :
    ∃p∈all c stack env,Produces p (.«VEC.TERNARYBITS» op) := by
  refine ⟨ConstructiveBodyOperatorProductions.vecTernarybits c stack env,?_,?_⟩
  · apply List.mem_append_left
    apply List.mem_append_right
    simp
  · unfold ConstructiveBodyOperatorProductions.vecTernarybits
    apply ConstructiveBodyPayloadCoverage.mapped
    exact generate_support vvternops op

theorem compares (c : context) (stack : inferresulttype) (env : Env c) (op : relop_) :
    ∃p∈all c stack env,Produces p (.COMPARE op) := by
  refine ⟨ConstructiveBodyOperatorProductions.compares c stack env (numericType op),?_,?_⟩
  · apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨numericType op,by cases op <;> simp [numericType],?_⟩
    simp
  · unfold ConstructiveBodyOperatorProductions.compares
    apply ConstructiveBodyPayloadCoverage.mapped (a:=(⟨op,rfl⟩ : {v : relop_ // numericType v=numericType op}))
    exact numericPayloads_complete domain_irelop domain_irelop domain_frelop domain_frelop op

theorem binaries (c : context) (stack : inferresulttype) (env : Env c) (op : binop_) :
    ∃p∈all c stack env,Produces p (.BINOP op) := by
  refine ⟨ConstructiveBodyOperatorProductions.binaries c stack env (numericType op),?_,?_⟩
  · apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨numericType op,by cases op <;> simp [numericType],?_⟩
    simp
  · unfold ConstructiveBodyOperatorProductions.binaries
    apply ConstructiveBodyPayloadCoverage.mapped (a:=(⟨op,rfl⟩ : {v : binop_ // numericType v=numericType op}))
    exact numericPayloads_complete domain_ibinop domain_ibinop domain_fbinop domain_fbinop op

theorem test (c : context) (stack : inferresulttype) (env : Env c) (op : testop_) :
    ∃p∈all c stack env,Produces p (.TEST op) := by
  cases op with
  | I32 op =>
    refine ⟨testI32 c stack env,?_,?_⟩
    · apply List.mem_append_left; apply List.mem_append_right; simp
    · unfold testI32
      apply ConstructiveBodyPayloadCoverage.mapped
      exact generate_support domain_itestop op
  | I64 op =>
    refine ⟨testI64 c stack env,?_,?_⟩
    · apply List.mem_append_left; apply List.mem_append_right; simp
    · unfold testI64
      apply ConstructiveBodyPayloadCoverage.mapped
      exact generate_support domain_itestop op
  | F32 op => cases op
  | F64 op => cases op

theorem splat (c : context) (stack : inferresulttype) (env : Env c) (op : vsplatop_) :
    ∃p∈all c stack env,Produces p (.«VEC.SPLAT» op) := by
  have hop : op∈([.V128 (.I8x16 .Splat),.V128 (.I16x8 .Splat),.V128 (.I32x4 .Splat),
    .V128 (.I64x2 .Splat),.V128 (.F32x4 .Splat),.V128 (.F64x2 .Splat)] : List vsplatop_) := by
    cases op with | V128 op => cases op <;> rename_i op <;> cases op <;> simp
  let p := production c stack env [.NumT (vecLaneType op)] [.VecT .V128T]
    (by intro t ht; rcases List.mem_singleton.mp ht with rfl; rfl)
    (by intro t ht; rcases List.mem_singleton.mp ht with rfl; rfl)
    (Audited.pure ()) (fun _ => .«VEC.SPLAT» op) (fun _ n => ConstructiveBodyOperatorCalls.vecSplat c stack op n)
  refine ⟨p,List.mem_append_right _ (List.mem_map.mpr ⟨op,hop,rfl⟩),?_⟩
  apply ConstructiveBodyPayloadCoverage.mapped (a:=())
  rfl

#print axioms test
#print axioms splat
end properties.wasm_module_ok.ConstructiveBodyOperatorCoverage
