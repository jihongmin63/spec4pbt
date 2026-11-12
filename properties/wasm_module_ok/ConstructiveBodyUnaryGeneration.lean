import properties.wasm_module_ok.ConstructiveBodyUnary
import properties.wasm_module_ok.ConstructiveBodyCertifiedChoice
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyUnaryGeneration
open SpecTec properties.wasm_module_ok ConstructiveConstTableCore
open ConstructiveBodyOperatorTypes ConstructiveBodyUnary ConstructiveBodyEnvironment ConstructiveBodyProductions

def first : numtype → unop_
  | .I32T => .I32 .Clz
  | .I64T => .I64 .Clz
  | .F32T => .F32 .Neg
  | .F64T => .F64 .Neg

def rest : numtype → List unop_
  | .I32T => [.I32 .Ctz,.I32 .Popcnt,.I32 (.ExtendS .I8),.I32 (.ExtendS .I16)]
  | .I64T => [.I64 .Ctz,.I64 .Popcnt,.I64 (.ExtendS .I8),.I64 (.ExtendS .I16),.I64 (.ExtendS .I32)]
  | .F32T => ConstructiveBodyOperatorEnums.domain_funop.rest.map .F32
  | .F64T => ConstructiveBodyOperatorEnums.domain_funop.rest.map .F64

theorem valid (nt : numtype) (op : unop_) (h : op∈first nt::rest nt) :
    numericType op=nt ∧ legal op=true := by
  cases nt <;> simp only [first,rest,ConstructiveBodyOperatorEnums.domain_funop,List.map_cons,List.map_nil,
    List.mem_cons,List.not_mem_nil,or_false] at h <;>
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨rfl,rfl⟩

def payloads (nt : numtype) : Audited {op : unop_ // numericType op=nt ∧ legal op=true} :=
  ConstructiveBodyCertifiedChoice.choose (first nt) (rest nt) (valid nt)

theorem covered (op : unop_) (h : legal op=true) : op∈first (numericType op)::rest (numericType op) := by
  cases op <;> rename_i u <;> cases u <;>
    simp_all [first,rest,numericType,legal,ConstructiveBodyOperatorEnums.domain_funop]
  all_goals rename_i pt; cases pt <;> simp_all [first,rest,numericType,legal]

theorem payloads_complete (op : unop_) (h : legal op=true) :
    Gen.support (payloads (numericType op)).generator ⟨op,rfl,h⟩ :=
  ConstructiveBodyCertifiedChoice.complete _ _ _ _ (covered op h)

theorem unary (c : context) (stack : inferresulttype) (op : unop_) (n : Nat) (h : legal op=true) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.UNARY op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.NumT (numericType op)] [.NumT (numericType op)] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.UNARY op) 81 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Instr_ok:clause:81» c stack (.UNARY op)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:81»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success ((unop_exact op n n).2 ⟨h,rfl⟩)
  apply SpecTecExecution.Eval.bind_success (numeric_type_call op n)
  exact SpecTecExecution.Eval.pure _

theorem original (c : context) (stack : inferresulttype) (op : unop_) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.UNARY op)⟩)
      n (.success (.of result)) finish) :
    legal op=true ∧ result=ConstructiveBodyControl.effect [.NumT (numericType op)] [.NumT (numericType op)] [] ∧ finish=n := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.UNARY op) 81 (by decide) rfl (by decide) result n finish).1 h
  have hl : legal op=true := by
    change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:81» c stack (.UNARY op)) n _ finish at hs
    unfold SpecTec.«Instr_ok:clause:81» at hs
    cases hs with | bind_success hg tail =>
     cases hg
     cases tail with | bind_success hu _ => exact ((unop_exact op _ _).1 hu).1
  exact ⟨hl,ConstructiveBodyOperatorCalls.effect_unique c stack (.UNARY op) _ result n finish (unary c stack op n hl) h⟩

def production (c : context) (stack : inferresulttype) (env : Env c) (nt : numtype) : Production c stack :=
  ConstructiveBodyOperatorProductions.production c stack env [.NumT nt] [.NumT nt]
    (by intro t ht; rcases List.mem_singleton.mp ht with rfl; rfl)
    (by intro t ht; rcases List.mem_singleton.mp ht with rfl; rfl)
    (payloads nt) (fun op => .UNARY op.val)
    (by intro op n; simpa only [op.property.1] using unary c stack op.val n op.property.2)

def all (c : context) (stack : inferresulttype) (env : Env c) : List (Production c stack) :=
  [.I32T,.I64T,.F32T,.F64T].map (production c stack env)

#print axioms payloads_complete
#print axioms original
end properties.wasm_module_ok.ConstructiveBodyUnaryGeneration
