import properties.wasm_module_ok.ConstructiveBodyOperatorCalls
import properties.wasm_module_ok.ConstructiveBodyOperatorDomains
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyOperatorProductions
open SpecTec properties.wasm_module_ok ConstructiveConstTableCore ConstructiveBodyOperatorEnums ConstructiveBodyOperatorDomains
open ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyOperatorTypes

/-- These payloads are selected only after the stack signature has been chosen. -/
def numericPayloads {A B C D : Type} (a : Domain A) (b : Domain B) (c : Domain C) (d : Domain D) :
    (t : numtype) → Audited {v : op A B C D // numericType v=t}
  | .I32T => (generate a).map fun v => ⟨.I32 v,rfl⟩
  | .I64T => (generate b).map fun v => ⟨.I64 v,rfl⟩
  | .F32T => (generate c).map fun v => ⟨.F32 v,rfl⟩
  | .F64T => (generate d).map fun v => ⟨.F64 v,rfl⟩

theorem numericPayloads_complete {A B C D : Type} (a : Domain A) (b : Domain B) (c : Domain C) (d : Domain D)
    (v : op A B C D) :
    Gen.support (numericPayloads a b c d (numericType v)).generator ⟨v,rfl⟩ := by
  cases v <;> simp only [numericType,numericPayloads,Audited.map,Gen.Support.support_map] <;>
    exact ⟨_,generate_support _ _,rfl⟩

abbrev Plain (t : valtype) : Prop := ReadyMatchReachability.sourceValHeaptypes t=[]
theorem plain_backed (c : context) (ts : List valtype) (h : ∀t∈ts,Plain t) :
    StackBacked c (.NoEllipses,ts) := by
  intro t ht heap hm
  rw [h t ht] at hm
  cases hm

def production {α : Type} (c : context) (stack : inferresulttype) (env : Env c)
    (ins outs : List valtype) (hi : ∀t∈ins,Plain t) (ho : ∀t∈outs,Plain t)
    (g : Audited α) (make : α → instr)
    (sound : ∀a n,SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (make a)⟩)
      n (.success (.of (ConstructiveBodyControl.effect ins outs []))) n) : Production c stack :=
  ConstructiveBodySimpleAtoms.unchanged c stack env (.NoEllipses,ins) (.NoEllipses,outs)
    (plain_backed c ins hi) (plain_backed c outs ho)
    (g.map fun a => ⟨make a,sound a⟩)

def compares (c : context) (stack : inferresulttype) (env : Env c) (nt : numtype) : Production c stack :=
  production c stack env [.NumT nt,.NumT nt] [.NumT .I32T]
    (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl; all_goals rfl) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl)
    (numericPayloads domain_irelop domain_irelop domain_frelop domain_frelop nt) (fun v => .COMPARE v.val)
    (by intro v n; simpa only [←v.property] using ConstructiveBodyOperatorCalls.compare c stack v.val n)

def binaries (c : context) (stack : inferresulttype) (env : Env c) (nt : numtype) : Production c stack :=
  production c stack env [.NumT nt,.NumT nt] [.NumT nt]
    (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl; all_goals rfl) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl)
    (numericPayloads domain_ibinop domain_ibinop domain_fbinop domain_fbinop nt) (fun v => .BINOP v.val)
    (by intro v n; simpa only [←v.property] using ConstructiveBodyOperatorCalls.binary c stack v.val n)

def testI32 (c : context) (stack : inferresulttype) (env : Env c) : Production c stack :=
  production c stack env [.NumT .I32T] [.NumT .I32T]
    (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl)
    (generate domain_itestop) (fun op => .TEST (.I32 op))
    (fun op n => ConstructiveBodyOperatorCalls.test c stack (.I32 op) n)

def testI64 (c : context) (stack : inferresulttype) (env : Env c) : Production c stack :=
  production c stack env [.NumT .I64T] [.NumT .I32T]
    (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl)
    (generate domain_itestop) (fun op => .TEST (.I64 op))
    (fun op n => ConstructiveBodyOperatorCalls.test c stack (.I64 op) n)

def vecTest (c : context) (stack : inferresulttype) (env : Env c) : Production c stack :=
  production c stack env [.VecT .V128T] [.NumT .I32T]
    (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl)
    (generate vec_tests) (fun op => .«VEC.TEST» op) (fun op n => ConstructiveBodyOperatorCalls.vecTest c stack op n)

def vecUnary (c : context) (stack : inferresulttype) (env : Env c) : Production c stack :=
  production c stack env [.VecT .V128T] [.VecT .V128T]
    (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl)
    (generate vec_unaries) (fun op => .«VEC.UNARY» op) (fun op n => ConstructiveBodyOperatorCalls.vecUnary c stack op n)

def vecTernary (c : context) (stack : inferresulttype) (env : Env c) : Production c stack :=
  production c stack env [.VecT .V128T,.VecT .V128T,.VecT .V128T] [.VecT .V128T]
    (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl|rfl; all_goals rfl) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl)
    (generate vec_ternaries) (fun op => .«VEC.TERNARY» op) (fun op n => ConstructiveBodyOperatorCalls.vecTernary c stack op n)

def vecCompare (c : context) (stack : inferresulttype) (env : Env c) : Production c stack :=
  production c stack env [.VecT .V128T,.VecT .V128T] [.VecT .V128T]
    (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl; all_goals rfl) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl)
    (generate vec_comparisons) (fun op => .«VEC.COMPARE» op) (fun op n => ConstructiveBodyOperatorCalls.vecCompare c stack op n)

def vecConvert (c : context) (stack : inferresulttype) (env : Env c) : Production c stack :=
  production c stack env [.VecT .V128T] [.VecT .V128T]
    (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl)
    (generate vec_conversions) (fun op => .«VEC.CONVERT» op) (fun op n => ConstructiveBodyOperatorCalls.vecConvert c stack op n)

def vecShift (c : context) (stack : inferresulttype) (env : Env c) : Production c stack :=
  production c stack env [.VecT .V128T,.NumT .I32T] [.VecT .V128T]
    (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl; all_goals rfl) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl)
    (generate vec_shifts) (fun op => .«VEC.SHIFT» op) (fun op n => ConstructiveBodyOperatorCalls.vecShift c stack op n)

def vecBitmask (c : context) (stack : inferresulttype) (env : Env c) : Production c stack :=
  production c stack env [.VecT .V128T] [.NumT .I32T]
    (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl)
    (generate vec_bitmasks) (fun op => .«VEC.BITMASK» op) (fun op n => ConstructiveBodyOperatorCalls.vecBitmask c stack op n)

def vecTestbits (c : context) (stack : inferresulttype) (env : Env c) : Production c stack :=
  production c stack env [.VecT .V128T] [.NumT .I32T]
    (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl)
    (generate vvtestops) (fun op => .«VEC.TESTBITS» op) (fun op n => ConstructiveBodyOperatorCalls.vecTestbits c stack op n)

def vecUnarybits (c : context) (stack : inferresulttype) (env : Env c) : Production c stack :=
  production c stack env [.VecT .V128T] [.VecT .V128T]
    (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl)
    (generate vvunops) (fun op => .«VEC.UNARYBITS» op) (fun op n => ConstructiveBodyOperatorCalls.vecUnarybits c stack op n)

def vecBinarybits (c : context) (stack : inferresulttype) (env : Env c) : Production c stack :=
  production c stack env [.VecT .V128T,.VecT .V128T] [.VecT .V128T]
    (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl; all_goals rfl) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl)
    (generate vvbinops) (fun op => .«VEC.BINARYBITS» op) (fun op n => ConstructiveBodyOperatorCalls.vecBinarybits c stack op n)

def vecTernarybits (c : context) (stack : inferresulttype) (env : Env c) : Production c stack :=
  production c stack env [.VecT .V128T,.VecT .V128T,.VecT .V128T] [.VecT .V128T]
    (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl|rfl; all_goals rfl) (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl; all_goals rfl)
    (generate vvternops) (fun op => .«VEC.TERNARYBITS» op) (fun op n => ConstructiveBodyOperatorCalls.vecTernarybits c stack op n)

def splats (c : context) (stack : inferresulttype) (env : Env c) : List (Production c stack) :=
  ([.V128 (.I8x16 .Splat),.V128 (.I16x8 .Splat),.V128 (.I32x4 .Splat),
    .V128 (.I64x2 .Splat),.V128 (.F32x4 .Splat),.V128 (.F64x2 .Splat)] : List vsplatop_).map fun op =>
    production c stack env [.NumT (vecLaneType op)] [.VecT .V128T]
      (by intro t ht; rcases List.mem_singleton.mp ht with rfl; rfl)
      (by intro t ht; rcases List.mem_singleton.mp ht with rfl; rfl)
      (Audited.pure ()) (fun _ => .«VEC.SPLAT» op) (fun _ n => ConstructiveBodyOperatorCalls.vecSplat c stack op n)

def all (c : context) (stack : inferresulttype) (env : Env c) : List (Production c stack) :=
  ([.I32T,.I64T,.F32T,.F64T].flatMap fun nt => [compares c stack env nt,binaries c stack env nt]) ++
  [testI32 c stack env,testI64 c stack env,
    vecTest c stack env,
    vecUnary c stack env,
    vecTernary c stack env,
    vecCompare c stack env,
    vecConvert c stack env,
    vecShift c stack env,
    vecBitmask c stack env,
    vecTestbits c stack env,
    vecUnarybits c stack env,
    vecBinarybits c stack env,
    vecTernarybits c stack env] ++ splats c stack env

#print axioms numericPayloads_complete
end properties.wasm_module_ok.ConstructiveBodyOperatorProductions
