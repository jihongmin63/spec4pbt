import properties.wasm_module_ok.ConstructiveBodyGeneration
import properties.wasm_module_ok.ConstructiveBodyPayloadCoverage
import properties.wasm_module_ok.ConstructiveBodyOperatorCoverage
import properties.wasm_module_ok.ConstructiveBodyRestrictedCoverage
import properties.wasm_module_ok.ConstructiveBodyIndexedComplete
import properties.wasm_module_ok.ConstructiveBodyLocalCoverage
import properties.wasm_module_ok.ConstructiveBodyBranchTableCoverage
import properties.wasm_module_ok.ConstructiveBodyFunctionCoverage
import properties.wasm_module_ok.ConstructiveBodyBulkCoverage
import properties.wasm_module_ok.ConstructiveBodyReferenceCoverage
import properties.wasm_module_ok.ConstructiveBodyCasts
import properties.wasm_module_ok.ConstructiveBodySelectCoverage
import properties.wasm_module_ok.ConstructiveBodyReferenceBranchCoverage
import properties.wasm_module_ok.ConstructiveBodyMemoryCoverage
import properties.wasm_module_ok.ConstructiveBodyAggregateNewCoverage
import properties.wasm_module_ok.ConstructiveBodyAggregateCoverage
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace properties.wasm_module_ok.ConstructiveBodyAtomicCoverage
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyProductionCoverage ConstructiveBodyGeneration

/-- Only a proof partition: control forms are covered by recursive body support. -/
def Atomic : instr → Prop
  | .BLOCK _ _ | .LOOP _ _ | .«IF % % ELSE %» _ _ _ | .TRY_TABLE _ _ _ => False
  | _ => True

def arity : instr → Nat
  | .«ARRAY.NEW_FIXED» _ count => count
  | _ => 0

theorem lift {c : context} {stack : inferresulttype} {ps qs : List (Production c stack)}
    {i : instr} {effect : inferinstrtype} {n finish : Nat}
    (h : Covers ps i effect ∧ finish=n) (hm : ∀p∈ps,p∈qs) : Covers qs i effect ∧ finish=n := by
  obtain ⟨⟨p,hp,he,hi⟩,hn⟩ := h
  exact ⟨⟨p,hm p hp,he,hi⟩,hn⟩

theorem realize {c : context} {stack : inferresulttype} {ps : List (Production c stack)}
    {i : instr} {effect : inferinstrtype} {n finish : Nat}
    (hr : ∃p∈ps,Produces p i)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack i⟩)
      n (.success (.of effect)) finish) : Covers ps i effect ∧ finish=n := by
  obtain ⟨p,hp,hi⟩ := hr
  exact ConstructiveBodyFunctionCoverage.from_production c stack ps p i effect n finish hp hi h

theorem original (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (i : instr) (ha : Atomic i) (depth : Nat) (hd : arity i≤depth) (child : ConstructiveBodyControlProductions.Builder)
    (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack i⟩)
      n (.success (.of effect)) finish) : Covers (catalog c stack env hs depth child) i effect ∧ finish=n := by
  cases i with
  | UNREACHABLE =>
    apply lift (realize (ConstructiveBodyPayloadCoverage.unreachable c stack env hs) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hp))))))))))))))))))))
  | NOP =>
    apply lift (realize (ConstructiveBodyPayloadCoverage.nop c stack env hs) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hp))))))))))))))))))))
  | DROP =>
    apply lift (realize (ConstructiveBodyPayloadCoverage.drop c stack env hs) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hp))))))))))))))))))))
  | SELECT x0 =>
    apply lift (ConstructiveBodySelectCoverage.original c stack env hs x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))
  | BLOCK x0 x1 =>
    exact False.elim ha
  | LOOP x0 x1 =>
    exact False.elim ha
  | «IF % % ELSE %» x0 x1 x2 =>
    exact False.elim ha
  | BR x0 =>
    apply lift (ConstructiveBodyIndexedComplete.branch c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))))
  | BR_IF x0 =>
    apply lift (ConstructiveBodyIndexedComplete.branchIf c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))))
  | BR_TABLE x0 x1 =>
    apply lift (ConstructiveBodyBranchTableCoverage.original c stack env hs x0 x1 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))))))))))))
  | BR_ON_NULL x0 =>
    apply lift (ConstructiveBodyReferenceBranchCoverage.onNull c stack env hs x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))))))
  | BR_ON_NON_NULL x0 =>
    apply lift (ConstructiveBodyReferenceBranchCoverage.onNonNull c stack env hs x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))))))
  | BR_ON_CAST x0 x1 x2 =>
    apply lift (ConstructiveBodyReferenceBranchCoverage.onCast c stack env hs x0 x1 x2 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))))))
  | BR_ON_CAST_FAIL x0 x1 x2 =>
    apply lift (ConstructiveBodyReferenceBranchCoverage.onCastFail c stack env hs x0 x1 x2 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))))))
  | CALL x0 =>
    apply lift (ConstructiveBodyFunctionCoverage.direct_original c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))
  | CALL_REF x0 =>
    apply lift (ConstructiveBodyFunctionCoverage.reference_original c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))
  | CALL_INDIRECT x0 x1 =>
    apply lift (ConstructiveBodyFunctionCoverage.indirect_original c stack env x0 x1 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))
  | RETURN =>
    apply lift (realize (ConstructiveBodyPayloadCoverage.returnValue c stack env hs) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hp))))))))))))))))))))
  | RETURN_CALL x0 =>
    apply lift (ConstructiveBodyFunctionCoverage.returnDirect_original c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))
  | RETURN_CALL_REF x0 =>
    apply lift (ConstructiveBodyFunctionCoverage.returnReference_original c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))
  | RETURN_CALL_INDIRECT x0 x1 =>
    apply lift (ConstructiveBodyFunctionCoverage.returnIndirect_original c stack env x0 x1 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))
  | THROW x0 =>
    apply lift (ConstructiveBodyFunctionCoverage.throwTag_original c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))
  | THROW_REF =>
    apply lift (realize (ConstructiveBodyPayloadCoverage.throwRef c stack env hs) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hp))))))))))))))))))))
  | TRY_TABLE x0 x1 x2 =>
    exact False.elim ha
  | «LOCAL.GET» x0 =>
    apply lift (ConstructiveBodyLocalCoverage.get_original c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))))))))))))))
  | «LOCAL.SET» x0 =>
    apply lift (ConstructiveBodyLocalCoverage.set_original c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))))))))))))))
  | «LOCAL.TEE» x0 =>
    apply lift (ConstructiveBodyLocalCoverage.tee_original c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))))))))))))))
  | «GLOBAL.GET» x0 =>
    apply lift (ConstructiveBodyIndexedComplete.globalGet c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))))
  | «GLOBAL.SET» x0 =>
    apply lift (ConstructiveBodyIndexedComplete.globalSet c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))))
  | «TABLE.GET» x0 =>
    apply lift (ConstructiveBodyIndexedComplete.tableGet c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))))
  | «TABLE.SET» x0 =>
    apply lift (ConstructiveBodyIndexedComplete.tableSet c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))))
  | «TABLE.SIZE» x0 =>
    apply lift (ConstructiveBodyIndexedComplete.tableSize c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))))
  | «TABLE.GROW» x0 =>
    apply lift (ConstructiveBodyIndexedComplete.tableGrow c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))))
  | «TABLE.FILL» x0 =>
    apply lift (ConstructiveBodyIndexedComplete.tableFill c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))))
  | «TABLE.COPY» x0 x1 =>
    apply lift (ConstructiveBodyBulkCoverage.tableCopy_original c stack env x0 x1 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))))))))))
  | «TABLE.INIT» x0 x1 =>
    apply lift (ConstructiveBodyBulkCoverage.tableInit_original c stack env x0 x1 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))))))))))
  | «ELEM.DROP» x0 =>
    apply lift (ConstructiveBodyIndexedComplete.elemDrop c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))))
  | LOAD x0 x1 =>
    apply lift (ConstructiveBodyMemoryCoverage.load c stack env x0 x1 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))
  | STORE x0 x1 =>
    apply lift (ConstructiveBodyMemoryCoverage.store c stack env x0 x1 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))
  | «VEC.LOAD» x0 x1 =>
    apply lift (ConstructiveBodyMemoryCoverage.vload c stack env x0 x1 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))
  | «VEC.STORE» x0 x1 =>
    apply lift (ConstructiveBodyMemoryCoverage.vstore c stack env x0 x1 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))
  | «VEC.LOAD_LANE» x0 x1 x2 =>
    apply lift (ConstructiveBodyMemoryCoverage.laneLoad c stack env x0 x1 x2 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))
  | «VEC.STORE_LANE» x0 x1 x2 =>
    apply lift (ConstructiveBodyMemoryCoverage.laneStore c stack env x0 x1 x2 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))
  | «MEMORY.SIZE» x0 =>
    apply lift (ConstructiveBodyIndexedComplete.memorySize c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))))
  | «MEMORY.GROW» x0 =>
    apply lift (ConstructiveBodyIndexedComplete.memoryGrow c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))))
  | «MEMORY.FILL» x0 =>
    apply lift (ConstructiveBodyIndexedComplete.memoryFill c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))))
  | «MEMORY.COPY» x0 x1 =>
    apply lift (ConstructiveBodyBulkCoverage.memoryCopy_original c stack env x0 x1 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))))))))))
  | «MEMORY.INIT» x0 x1 =>
    apply lift (ConstructiveBodyBulkCoverage.memoryInit_original c stack env x0 x1 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))))))))))
  | «DATA.DROP» x0 =>
    apply lift (ConstructiveBodyIndexedComplete.dataDrop c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))))))
  | «REF.NULL» x0 =>
    apply lift (ConstructiveBodyReferenceCoverage.nullRef_original c stack env hs x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))
  | «REF.FUNC» x0 =>
    apply lift (ConstructiveBodyReferenceCoverage.funcRef_original c stack env hs x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))
  | «REF.IS_NULL» =>
    apply lift (ConstructiveBodyReferenceCoverage.isNull_original c stack env hs effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))
  | «REF.AS_NON_NULL» =>
    apply lift (ConstructiveBodyReferenceCoverage.asNonNull_original c stack env hs effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))
  | «REF.TEST» x0 =>
    apply lift (ConstructiveBodyCasts.testRef_original c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))))))))
  | «REF.CAST» x0 =>
    apply lift (ConstructiveBodyCasts.castRef_original c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))))))))
  | «REF.EQ» =>
    apply lift (ConstructiveBodyReferenceCoverage.equal_original c stack env hs effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))
  | «REF.I31» =>
    apply lift (ConstructiveBodyReferenceCoverage.i31_original c stack env hs effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))
  | «I31.GET» x0 =>
    apply lift (ConstructiveBodyReferenceCoverage.getI31_original c stack env hs x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))
  | «STRUCT.NEW» x0 x1 =>
    cases x1 with
    | Explicit =>
      apply lift (ConstructiveBodyAggregateNewCoverage.structExplicit c stack env x0 effect n finish depth h)
      intro p hp
      simp only [catalog,List.mem_append,List.mem_singleton]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))))
    | Implicit =>
      apply lift (ConstructiveBodyAggregateNewCoverage.structImplicit c stack env x0 effect n finish depth h)
      intro p hp
      simp only [catalog,List.mem_append,List.mem_singleton]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))))
  | «STRUCT.GET» x0 x1 x2 =>
    cases x2 with
    | none =>
      apply lift (ConstructiveBodyAggregateCoverage.structGetNone_original c stack env x0 x1 effect n finish h)
      intro p hp
      simp only [catalog,List.mem_append,List.mem_singleton]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))
    | some ext =>
      apply lift (ConstructiveBodyAggregateCoverage.structGetSome_original c stack env x0 x1 ext effect n finish h)
      intro p hp
      simp only [catalog,List.mem_append,List.mem_singleton]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))
  | «STRUCT.SET» x0 x1 =>
    apply lift (ConstructiveBodyAggregateCoverage.structSet_original c stack env x0 x1 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))
  | «ARRAY.NEW» x0 x1 =>
    cases x1 with
    | Explicit =>
      apply lift (ConstructiveBodyAggregateNewCoverage.arrayExplicit c stack env x0 effect n finish depth h)
      intro p hp
      simp only [catalog,List.mem_append,List.mem_singleton]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))))
    | Implicit =>
      apply lift (ConstructiveBodyAggregateNewCoverage.arrayImplicit c stack env x0 effect n finish depth h)
      intro p hp
      simp only [catalog,List.mem_append,List.mem_singleton]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))))
  | «ARRAY.NEW_FIXED» x0 x1 =>
    apply lift (ConstructiveBodyAggregateNewCoverage.arrayFixed c stack env x0 x1 effect n finish depth hd h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))))
  | «ARRAY.NEW_ELEM» x0 x1 =>
    apply lift (ConstructiveBodyAggregateCoverage.newElem_original c stack env x0 x1 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))
  | «ARRAY.NEW_DATA» x0 x1 =>
    apply lift (ConstructiveBodyAggregateCoverage.newData_original c stack env x0 x1 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))
  | «ARRAY.GET» x0 x1 =>
    cases x1 with
    | none =>
      apply lift (ConstructiveBodyAggregateCoverage.arrayGetNone_original c stack env x0 effect n finish h)
      intro p hp
      simp only [catalog,List.mem_append,List.mem_singleton]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))
    | some ext =>
      apply lift (ConstructiveBodyAggregateCoverage.arrayGetSome_original c stack env x0 ext effect n finish h)
      intro p hp
      simp only [catalog,List.mem_append,List.mem_singleton]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))
  | «ARRAY.SET» x0 =>
    apply lift (ConstructiveBodyAggregateCoverage.arraySet_original c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))
  | «ARRAY.LEN» =>
    apply lift (ConstructiveBodyReferenceCoverage.arrayLength_original c stack env hs effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))
  | «ARRAY.COPY» x0 x1 =>
    apply lift (ConstructiveBodyAggregateCoverage.copy_original c stack env x0 x1 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))
  | «ARRAY.FILL» x0 =>
    apply lift (ConstructiveBodyAggregateCoverage.arrayFill_original c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))
  | «ARRAY.INIT_DATA» x0 x1 =>
    apply lift (ConstructiveBodyAggregateCoverage.initData_original c stack env x0 x1 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))
  | «ARRAY.INIT_ELEM» x0 x1 =>
    apply lift (ConstructiveBodyAggregateCoverage.initElem_original c stack env x0 x1 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))
  | «EXTERN.CONVERT» x0 =>
    apply lift (ConstructiveBodyReferenceCoverage.externConvert_original c stack env hs x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))))))))
  | CONST x0 =>
    apply lift (realize (ConstructiveBodyPayloadCoverage.numeric c stack env x0) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))
  | TEST x0 =>
    apply lift (realize (ConstructiveBodyOperatorCoverage.test c stack env x0) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))
  | COMPARE x0 =>
    apply lift (realize (ConstructiveBodyOperatorCoverage.compares c stack env x0) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))
  | UNARY x0 =>
    apply lift (ConstructiveBodyRestrictedCoverage.unary c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))
  | BINOP x0 =>
    apply lift (realize (ConstructiveBodyOperatorCoverage.binaries c stack env x0) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))
  | CONVERT x0 =>
    apply lift (ConstructiveBodyRestrictedCoverage.conversion c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))
  | «VEC.CONST» x0 =>
    apply lift (realize (ConstructiveBodyPayloadCoverage.vector c stack env x0) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))
  | «VEC.TEST» x0 =>
    apply lift (realize (ConstructiveBodyOperatorCoverage.vecTest c stack env x0) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))
  | «VEC.UNARY» x0 =>
    apply lift (realize (ConstructiveBodyOperatorCoverage.vecUnary c stack env x0) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))
  | «VEC.BINARY» x0 =>
    apply lift (ConstructiveBodyRestrictedCoverage.vectorBinary c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    have hp := List.mem_singleton.mp hp
    exact Or.inl (Or.inl (Or.inl (Or.inr hp)))
  | «VEC.TERNARY» x0 =>
    apply lift (realize (ConstructiveBodyOperatorCoverage.vecTernary c stack env x0) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))
  | «VEC.COMPARE» x0 =>
    apply lift (realize (ConstructiveBodyOperatorCoverage.vecCompare c stack env x0) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))
  | «VEC.CONVERT» x0 =>
    apply lift (realize (ConstructiveBodyOperatorCoverage.vecConvert c stack env x0) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))
  | «VEC.SHIFT» x0 =>
    apply lift (realize (ConstructiveBodyOperatorCoverage.vecShift c stack env x0) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))
  | «VEC.BITMASK» x0 =>
    apply lift (realize (ConstructiveBodyOperatorCoverage.vecBitmask c stack env x0) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))
  | «VEC.TESTBITS» x0 =>
    apply lift (realize (ConstructiveBodyOperatorCoverage.vecTestbits c stack env x0) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))
  | «VEC.UNARYBITS» x0 =>
    apply lift (realize (ConstructiveBodyOperatorCoverage.vecUnarybits c stack env x0) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))
  | «VEC.BINARYBITS» x0 =>
    apply lift (realize (ConstructiveBodyOperatorCoverage.vecBinarybits c stack env x0) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))
  | «VEC.TERNARYBITS» x0 =>
    apply lift (realize (ConstructiveBodyOperatorCoverage.vecTernarybits c stack env x0) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))
  | «VEC.SPLAT» x0 =>
    apply lift (realize (ConstructiveBodyOperatorCoverage.splat c stack env x0) h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))
  | «VEC.EXTRACT» x0 =>
    apply lift (ConstructiveBodyRestrictedCoverage.extract c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inr hp))
  | «VEC.REPLACE» x0 =>
    apply lift (ConstructiveBodyRestrictedCoverage.replace c stack env x0 effect n finish h)
    intro p hp
    simp only [catalog,List.mem_append,List.mem_singleton]
    exact Or.inl (Or.inl (Or.inr hp))

#print axioms original
end properties.wasm_module_ok.ConstructiveBodyAtomicCoverage
